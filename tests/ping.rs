// SPDX-FileCopyrightText: Robin Krahl <robin.krahl@ireas.org>
// SPDX-License-Identifier: CC0-1.0

use std::{thread, time::Duration};

use crossbeam::channel;
use mock_usb_bus::Bus;
use usb_device02::{
    bus::{UsbBus, UsbBusAllocator},
    class::UsbClass,
    device::{UsbDeviceBuilder, UsbVidPid},
    endpoint::{EndpointAddress, EndpointIn, EndpointOut, EndpointType},
    UsbDirection, UsbError,
};

const BUFFER_LEN: u16 = 1024;

struct Ping<'a, B: UsbBus> {
    buffer: [u8; BUFFER_LEN as _],
    ep_out: EndpointOut<'a, B>,
    ep_in: EndpointIn<'a, B>,
}

impl<'a, B: UsbBus> Ping<'a, B> {
    fn new(bus: &'a UsbBusAllocator<B>) -> Result<Self, UsbError> {
        let ep_out = bus.alloc(None, EndpointType::Interrupt, BUFFER_LEN, 0)?;
        let ep_in = bus.alloc(None, EndpointType::Interrupt, BUFFER_LEN, 0)?;
        Ok(Self {
            buffer: [0; BUFFER_LEN as _],
            ep_out,
            ep_in,
        })
    }

    fn endpoint_read(&self) -> EndpointAddress {
        self.ep_out.address()
    }

    fn endpoint_write(&self) -> EndpointAddress {
        self.ep_in.address()
    }
}

impl<B: UsbBus> UsbClass<B> for Ping<'_, B> {
    fn endpoint_out(&mut self, addr: EndpointAddress) {
        if addr == self.endpoint_read() {
            let n = self
                .ep_out
                .read(&mut self.buffer)
                .expect("failed to read from endpoint");
            self.ep_in
                .write(&self.buffer[..n])
                .expect("failed to write to endpoint");
        }
    }
}

#[test]
fn test_endpoints() {
    let bus = UsbBusAllocator::new(Bus::default());

    let ping = Ping::new(&bus).unwrap();
    let endpoint_read = ping.endpoint_read();
    let endpoint_write = ping.endpoint_write();
    assert_eq!(endpoint_read.direction(), UsbDirection::Out);
    assert_eq!(endpoint_write.direction(), UsbDirection::In);

    let device = UsbDeviceBuilder::new(&bus, UsbVidPid(0, 0)).build();

    let endpoints: Vec<_> = device.bus().endpoints().collect();
    assert_eq!(endpoints.len(), 4);

    assert_eq!(endpoints[0].address.index(), 0);
    assert_eq!(endpoints[0].address.direction(), UsbDirection::Out.into());
    assert_eq!(endpoints[0].ty, EndpointType::Control.into());

    assert_eq!(endpoints[1].address, endpoint_read.into());
    assert_eq!(endpoints[1].ty, EndpointType::Interrupt.into());

    assert_eq!(endpoints[2].address.index(), 0);
    assert_eq!(endpoints[2].address.direction(), UsbDirection::In.into());
    assert_eq!(endpoints[2].ty, EndpointType::Control.into());

    assert_eq!(endpoints[3].address, endpoint_write.into());
    assert_eq!(endpoints[3].ty, EndpointType::Interrupt.into());
}

#[test]
fn test_device() {
    let bus = UsbBusAllocator::new(Bus::default());
    let mut ping = Ping::new(&bus).unwrap();
    let mut device = UsbDeviceBuilder::new(&bus, UsbVidPid(0, 0)).build();

    let (stop_tx, stop_rx) = channel::bounded(1);
    let tx = device
        .bus()
        .endpoint_tx(ping.endpoint_read().into())
        .unwrap();
    let rx = device
        .bus()
        .endpoint_rx(ping.endpoint_write().into())
        .unwrap();

    thread::scope(|s| {
        s.spawn(|| {
            while stop_rx.try_recv().is_err() {
                device.poll(&mut [&mut ping]);
                thread::sleep(Duration::from_millis(10));
            }
        });

        let data = b"my test data";
        tx.send(data.into()).unwrap();
        let reply = rx.recv().unwrap();
        assert_eq!(data.as_slice(), reply.as_slice());

        stop_tx.send(()).unwrap();
    });
}
