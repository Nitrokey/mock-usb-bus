// SPDX-FileCopyrightText: Robin Krahl <robin.krahl@ireas.org>
// SPDX-License-Identifier: Apache-2.0 or MIT

//! A mock USB bus implementation backed by [`crossbeam`][] channels.
//!
//! This crate provides the [`Bus`][] struct that implements the `usb_device::bus::UsbBus`
//! trait and can be used to test USB class implementations in software.
//!
//! This crate supports multiple versions of the `usb-device` crate behind these feature flags:
//! - `usb-device-v0.2`: [`usb-device` v0.2](`usb_device02`) ([`UsbBus`](`usb_device02::bus::UsbBus`))
//! - `usb-device-v0.3`: [`usb-device` v0.3](`usb_device03`) ([`UsbBus`](`usb_device03::bus::UsbBus`))
//!
//! Therefore some types from `usb-device` are duplicated in this crate:
//! - [`EndpointAddress`][]
//! - [`EndpointType`][]
//! - [`UsbDirection`][]
//!
//! They provide [`From`][] implementations for conversion from the `usb-device` types.
//!
//! # Example
//!
//! This example uses [`Bus`][] to create a USB device that writes back the data that it receives
//! (implemented by the `Ping` class).  For the full code, see `tests/ping.rs`.
//!
//! ```ignore
//! use mock_usb_bus::Bus;
//! use usb_device::{bus::UsbBusAllocator, device::{UsbDeviceBuilder, UsbVidPid}};
//!
//! let bus = UsbBusAllocator::new(Bus::default());
//! let mut ping = Ping::new(&bus);
//! let mut device = UsbDeviceBuilder::new(&bus, UsbVidPid(0, 0)).build();
//!
//! loop {
//!     device.poll(&mut [&mut ping]);
//! }
//! ```
//!
//! A different thread can then use the channels provided by [`Bus`][] to send data to and receive
//! data from the device:
//!
//! ```ignore
//! let tx = device.bus().endpoint_tx(ping.endpoint_read().into()).unwrap();
//! let rx = device.bus().endpoint_rx(ping.endpoint_write().into()).unwrap();
//!
//! let data = b"test data";
//! tx.send(data.into()).unwrap();
//! let reply = rx.recv().unwrap();
//! assert_eq!(data.as_slice(), reply.as_slice());
//! ```

#![warn(
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    non_ascii_idents,
    trivial_casts,
    unused,
    unused_qualifications
)]
#![deny(unsafe_code)]
// Allow dead code if none of the features using the implementation is activated.
#![cfg_attr(
    not(any(feature = "usb-device-v0.2", feature = "usb-device-v0.3",)),
    allow(unused)
)]

#[cfg(feature = "usb-device-v0.2")]
mod impl02;
#[cfg(feature = "usb-device-v0.3")]
mod impl03;

use std::{
    collections::{btree_map::Entry, BTreeMap},
    sync::atomic::{AtomicBool, Ordering},
};

use crossbeam::channel::{self, Receiver, Sender};

/// The direction of USB traffic.
#[derive(Clone, Copy, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub enum UsbDirection {
    /// Traffic from the host to the device.
    Out,
    /// Traffic from the device to the host.
    In,
}

/// The address of an endpoint.
///
/// An address consists of the [`UsbDirection`][] and an index.  As the address is encoded as a
/// `u8` with the highest bit indicating the direction, the index cannot be larger than 127.
#[derive(Clone, Copy, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub struct EndpointAddress {
    direction: UsbDirection,
    idx: u8,
}

impl EndpointAddress {
    /// Creates a new address from the given index and direction.
    ///
    /// The index must not be larger than 127.  Otherwise, this method returns `None`.
    pub const fn new(idx: u8, direction: UsbDirection) -> Option<Self> {
        // highest bit is used to store direction
        if idx.leading_zeros() >= 1 {
            Some(Self { direction, idx })
        } else {
            None
        }
    }

    /// Returns the direction of this endpoint.
    pub const fn direction(&self) -> UsbDirection {
        self.direction
    }

    /// Returns the index of this endpoint (< 128).
    pub const fn index(&self) -> u8 {
        self.idx
    }
}

/// The type of an endpoint.
#[derive(Clone, Copy, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
pub enum EndpointType {
    /// Control endpoint.
    Control,
    /// Isochronous endpoint.
    Isochronous,
    /// Bulk endpoint.
    Bulk,
    /// Interrupt endpoint.
    Interrupt,
}

/// Information about an allocated endpoint.
#[derive(Clone, Copy, Debug, Hash, Eq, Ord, PartialEq, PartialOrd)]
#[non_exhaustive]
pub struct Endpoint {
    /// The address of the endpoint.
    pub address: EndpointAddress,
    /// The type of the endpoint.
    pub ty: EndpointType,
}

#[derive(Debug)]
struct EndpointData {
    ty: EndpointType,
    tx: Sender<Vec<u8>>,
    rx: Receiver<Vec<u8>>,
    in_started: AtomicBool,
}

impl EndpointData {
    fn new(ty: EndpointType) -> Self {
        let (tx, rx) = channel::bounded(1);
        Self {
            ty,
            tx,
            rx,
            in_started: AtomicBool::new(false),
        }
    }
}

/// A mock USB bus implementation backed by [`crossbeam`][] channels.
///
/// This struct implements the `UsbBus` trait.  Use [`Bus::endpoints`][] to inspect the endpoints
/// that have been allocated on this bus.  Use [`Bus::endpoint_tx`][] and [`Bus::endpoint_rx`][]
/// to access the [`crossbeam`][] channels that are used to send data to and read data from the
/// device.
///
/// The following features are currently implemented:
/// - Allocating an endpoint (`UsbBus::alloc_ep`).  Indizes are assigned in ascending order
///   starting from 1.  Index 0 is only assigned if explicitly requested.  This also allocates a
///   channel for sending and receiving data.  Note that this channel has capacity 1.
/// - Enabling the bus (`UsbBus::enable`).  This makes it impossible to allocate more endpoints.
/// - Reading data (`UsbBus::read`).  Returns data from the channel of OUT endpoints.
/// - Writing data (`UsbBus::write`).  Writes data to the channel of IN endpoints.
/// - Polling (`UsbBus::poll`).  Returns `PollResult::Data` with `ep_out` and `ep_in_complete` set
///   based on the status of the endpoint channels, or `PollResult::None`.
///
/// All other `UsbBus` functions panic.
#[derive(Debug, Default)]
pub struct Bus {
    enabled: bool,
    endpoints: BTreeMap<EndpointAddress, EndpointData>,
}

impl Bus {
    /// Creates a new bus without endpoints.
    pub fn new() -> Self {
        Default::default()
    }

    /// Iterates over all allocated endpoints, sorted by address.
    pub fn endpoints(&self) -> impl Iterator<Item = Endpoint> + '_ {
        self.endpoints.iter().map(|(&address, endpoint)| Endpoint {
            address,
            ty: endpoint.ty,
        })
    }

    /// Returns the sender for the given OUT endpoint.
    ///
    /// If no endpoint has been allocated with this address or if the endpoint does not have
    /// direction [`UsbDirection::Out`][], `None` is returned.
    pub fn endpoint_tx(&self, addr: EndpointAddress) -> Option<Sender<Vec<u8>>> {
        if addr.direction() == UsbDirection::Out {
            self.endpoints.get(&addr).map(|ep| ep.tx.clone())
        } else {
            None
        }
    }

    /// Returns the receiver for the given IN endpoint.
    ///
    /// If no endpoint has been allocated with this address or if the endpoint does not have
    /// direction [`UsbDirection::In`][], `None` is returned.
    pub fn endpoint_rx(&self, addr: EndpointAddress) -> Option<Receiver<Vec<u8>>> {
        if addr.direction() == UsbDirection::In {
            self.endpoints.get(&addr).map(|ep| ep.rx.clone())
        } else {
            None
        }
    }

    fn next_address(&self, direction: UsbDirection) -> Option<EndpointAddress> {
        let mut idx = 1;
        for key in self.endpoints.keys() {
            if key.direction() != direction {
                continue;
            }
            if key.index() == 0 {
                continue;
            }
            if key.index() == idx {
                idx = idx.checked_add(1)?;
            } else {
                break;
            }
        }
        EndpointAddress::new(idx, direction)
    }

    fn impl_alloc_ep(
        &mut self,
        ep_dir: UsbDirection,
        ep_addr: Option<EndpointAddress>,
        ep_type: EndpointType,
    ) -> Result<EndpointAddress, Error> {
        if self.enabled {
            return Err(Error::InvalidState);
        }

        let ep_addr = if let Some(ep_addr) = ep_addr {
            if ep_dir != ep_addr.direction() {
                return Err(Error::InvalidEndpoint);
            }
            ep_addr
        } else {
            self.next_address(ep_dir).ok_or(Error::EndpointOverflow)?
        };

        if let Entry::Vacant(e) = self.endpoints.entry(ep_addr) {
            e.insert(EndpointData::new(ep_type));
            Ok(ep_addr)
        } else {
            Err(Error::InvalidEndpoint)
        }
    }

    fn impl_enable(&mut self) {
        self.enabled = true;
    }

    fn impl_write(&self, ep_addr: EndpointAddress, buf: &[u8]) -> Result<usize, Error> {
        if ep_addr.direction() != UsbDirection::In {
            return Err(Error::InvalidEndpoint);
        }
        let n = buf.len();
        let endpoint = self.endpoints.get(&ep_addr).ok_or(Error::InvalidEndpoint)?;
        endpoint
            .tx
            .try_send(buf.into())
            .map_err(|_| Error::WouldBlock)?;
        endpoint.in_started.store(true, Ordering::Relaxed);
        Ok(n)
    }

    fn impl_read(&self, ep_addr: EndpointAddress, buf: &mut [u8]) -> Result<usize, Error> {
        if ep_addr.direction() != UsbDirection::Out {
            return Err(Error::InvalidEndpoint);
        }
        let packet = self
            .endpoints
            .get(&ep_addr)
            .ok_or(Error::InvalidEndpoint)?
            .rx
            .try_recv()
            .map_err(|_| Error::WouldBlock)?;
        let n = packet.len();
        if n <= buf.len() {
            buf[..n].copy_from_slice(&packet);
            Ok(n)
        } else {
            Err(Error::BufferOverflow)
        }
    }

    fn impl_poll(&self) -> PollResult {
        let mut ep_out = 0;
        let mut ep_in_complete = 0;
        for (ep_addr, endpoint) in &self.endpoints {
            match ep_addr.direction() {
                UsbDirection::Out => {
                    if !endpoint.rx.is_empty() {
                        ep_out |= 1 << ep_addr.index();
                    }
                }
                UsbDirection::In => {
                    if endpoint.tx.is_empty() && endpoint.in_started.swap(false, Ordering::Relaxed)
                    {
                        ep_in_complete |= 1 << ep_addr.index();
                    }
                }
            }
        }
        if ep_out > 0 || ep_in_complete > 0 {
            PollResult::Data {
                ep_out,
                ep_in_complete,
            }
        } else {
            PollResult::None
        }
    }
}

#[derive(Debug, PartialEq)]
enum PollResult {
    Data { ep_out: u16, ep_in_complete: u16 },
    None,
}

#[derive(Debug, PartialEq)]
enum Error {
    BufferOverflow,
    EndpointOverflow,
    InvalidEndpoint,
    InvalidState,
    WouldBlock,
}

#[cfg(test)]
mod tests {
    use super::{Bus, Endpoint, EndpointAddress, EndpointType, Error, PollResult, UsbDirection};

    #[test]
    fn test_address() {
        for direction in [UsbDirection::Out, UsbDirection::In] {
            for idx in [0, 1, 10, 127] {
                let address = EndpointAddress::new(idx, direction);
                assert_eq!(address, Some(EndpointAddress { direction, idx }));
                let address = address.unwrap();
                assert_eq!(address.direction(), direction);
                assert_eq!(address.index(), idx);
            }
            for idx in [128, 129, 230, u8::MAX] {
                assert_eq!(EndpointAddress::new(idx, direction), None);
            }
        }
    }

    #[test]
    fn test_address_order() {
        let out0 = EndpointAddress::new(0, UsbDirection::Out).unwrap();
        let out1 = EndpointAddress::new(1, UsbDirection::Out).unwrap();
        let out127 = EndpointAddress::new(127, UsbDirection::Out).unwrap();
        let in0 = EndpointAddress::new(0, UsbDirection::In).unwrap();
        let in1 = EndpointAddress::new(1, UsbDirection::In).unwrap();
        let in127 = EndpointAddress::new(127, UsbDirection::In).unwrap();

        let mut addresses = [in127, in1, in0, out127, out1, out0];
        addresses.sort();
        assert_eq!(addresses, [out0, out1, out127, in0, in1, in127,]);
    }

    fn alloc(
        bus: &mut Bus,
        direction: UsbDirection,
        addr: Option<u8>,
        ty: EndpointType,
    ) -> Result<EndpointAddress, Error> {
        bus.impl_alloc_ep(
            direction,
            addr.map(|idx| EndpointAddress::new(idx, direction).unwrap()),
            ty,
        )
    }

    fn alloc_ok(
        bus: &mut Bus,
        direction: UsbDirection,
        addr: Option<u8>,
        ty: EndpointType,
    ) -> EndpointAddress {
        let addr = alloc(bus, direction, addr, ty).unwrap();
        assert_eq!(addr.direction(), direction);
        addr
    }

    fn alloc_err(
        bus: &mut Bus,
        direction: UsbDirection,
        addr: Option<u8>,
        ty: EndpointType,
    ) -> Error {
        alloc(bus, direction, addr, ty).unwrap_err()
    }

    #[test]
    fn test_bus_alloc() {
        let mut bus = Bus::default();

        for direction in [UsbDirection::Out, UsbDirection::In] {
            let addr = alloc_ok(&mut bus, direction, None, EndpointType::Interrupt);
            assert_eq!(addr.index(), 1);
            let addr = alloc_ok(&mut bus, direction, None, EndpointType::Bulk);
            assert_eq!(addr.index(), 2);
            let err = alloc_err(&mut bus, direction, Some(1), EndpointType::Interrupt);
            assert_eq!(err, Error::InvalidEndpoint);
            let addr = alloc_ok(&mut bus, direction, Some(9), EndpointType::Bulk);
            assert_eq!(addr.index(), 9);
            let addr = alloc_ok(&mut bus, direction, None, EndpointType::Bulk);
            assert_eq!(addr.index(), 3);
            let addr = alloc_ok(&mut bus, direction, Some(0), EndpointType::Control);
            assert_eq!(addr.index(), 0);
            let addr = alloc_ok(&mut bus, direction, None, EndpointType::Bulk);
            assert_eq!(addr.index(), 4);
        }

        let expected = [
            (0, EndpointType::Control),
            (1, EndpointType::Interrupt),
            (2, EndpointType::Bulk),
            (3, EndpointType::Bulk),
            (4, EndpointType::Bulk),
            (9, EndpointType::Bulk),
        ];
        let endpoints: Vec<_> = bus.endpoints().collect();
        let mut expected_endpoints = Vec::new();
        for direction in [UsbDirection::Out, UsbDirection::In] {
            expected_endpoints.extend(expected.into_iter().map(|(idx, ty)| Endpoint {
                address: EndpointAddress::new(idx, direction).unwrap(),
                ty,
            }));
        }
        assert_eq!(endpoints, expected_endpoints);
    }

    #[test]
    fn test_bus_alloc_wrong_type() {
        let mut bus = Bus::default();

        let result = bus.impl_alloc_ep(
            UsbDirection::In,
            Some(EndpointAddress::new(0, UsbDirection::Out).unwrap()),
            EndpointType::Interrupt,
        );
        assert_eq!(result, Err(Error::InvalidEndpoint));

        let result = bus.impl_alloc_ep(
            UsbDirection::Out,
            Some(EndpointAddress::new(0, UsbDirection::In).unwrap()),
            EndpointType::Interrupt,
        );
        assert_eq!(result, Err(Error::InvalidEndpoint));
    }

    #[test]
    fn test_bus_alloc_overflow() {
        for direction in [UsbDirection::In, UsbDirection::Out] {
            let mut bus = Bus::default();
            for i in 1..128 {
                let addr = alloc_ok(&mut bus, direction, None, EndpointType::Interrupt);
                assert_eq!(addr.index(), i);
            }
            let err = alloc_err(&mut bus, direction, None, EndpointType::Interrupt);
            assert_eq!(err, Error::EndpointOverflow);
        }
    }

    #[test]
    fn test_bus_write() {
        let mut bus = Bus::default();

        let ep_in1 = alloc_ok(&mut bus, UsbDirection::In, Some(1), EndpointType::Interrupt);
        let ep_in2 = alloc_ok(&mut bus, UsbDirection::In, Some(2), EndpointType::Interrupt);
        let ep_in3 = EndpointAddress::new(3, UsbDirection::In).unwrap();
        let ep_out1 = alloc_ok(
            &mut bus,
            UsbDirection::Out,
            Some(1),
            EndpointType::Interrupt,
        );
        let ep_out2 = EndpointAddress::new(2, UsbDirection::Out).unwrap();

        let rx1 = bus.endpoint_rx(ep_in1).unwrap();
        let rx2 = bus.endpoint_rx(ep_in2).unwrap();

        assert!(bus.endpoint_rx(ep_in3).is_none());
        assert!(bus.endpoint_rx(ep_out1).is_none());
        assert!(bus.endpoint_rx(ep_out2).is_none());

        assert_eq!(bus.impl_poll(), PollResult::None);

        assert!(rx1.is_empty());
        assert!(rx2.is_empty());

        let data = b"testdata";
        let result = bus.impl_write(ep_in2, data);
        assert_eq!(result, Ok(data.len()));

        assert_eq!(bus.impl_poll(), PollResult::None);

        assert!(rx1.is_empty());
        assert!(!rx2.is_empty());

        let result = bus.impl_write(ep_in2, data);
        assert_eq!(result, Err(Error::WouldBlock));
        assert_eq!(bus.impl_poll(), PollResult::None);

        let received = rx2.recv().unwrap();
        assert_eq!(&received, data);

        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0,
                ep_in_complete: 0b100
            }
        );
        assert_eq!(bus.impl_poll(), PollResult::None);

        assert!(rx2.try_recv().is_err());
        assert_eq!(bus.impl_poll(), PollResult::None);
        assert!(bus.impl_write(ep_in2, data).is_ok());
    }

    #[test]
    fn test_bus_write_multi() {
        let mut bus = Bus::default();

        let ep_in1 = alloc_ok(&mut bus, UsbDirection::In, Some(1), EndpointType::Interrupt);
        let ep_in2 = alloc_ok(&mut bus, UsbDirection::In, Some(2), EndpointType::Interrupt);

        let rx1 = bus.endpoint_rx(ep_in1).unwrap();
        let rx2 = bus.endpoint_rx(ep_in2).unwrap();

        assert_eq!(bus.impl_poll(), PollResult::None);

        assert!(rx1.is_empty());
        assert!(rx2.is_empty());

        let data1 = b"testdata";
        let result = bus.impl_write(ep_in1, data1);
        assert_eq!(result, Ok(data1.len()));

        let data2 = b"some other important data";
        let result = bus.impl_write(ep_in2, data2);
        assert_eq!(result, Ok(data2.len()));

        assert_eq!(bus.impl_poll(), PollResult::None);

        assert!(!rx1.is_empty());
        assert!(!rx2.is_empty());

        assert_eq!(rx1.recv().unwrap(), data1);
        assert_eq!(rx2.recv().unwrap(), data2);

        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0,
                ep_in_complete: 0b110
            }
        );
        assert_eq!(bus.impl_poll(), PollResult::None);
    }

    #[test]
    fn test_bus_write_out() {
        let mut bus = Bus::default();

        let ep = alloc_ok(
            &mut bus,
            UsbDirection::Out,
            Some(1),
            EndpointType::Interrupt,
        );
        assert_eq!(bus.impl_write(ep, b"data"), Err(Error::InvalidEndpoint));
    }

    #[test]
    fn test_bus_write_unalloc() {
        let bus = Bus::default();

        let ep = EndpointAddress::new(3, UsbDirection::In).unwrap();
        assert_eq!(bus.impl_write(ep, b"data"), Err(Error::InvalidEndpoint));
    }

    #[test]
    fn test_bus_read() {
        let mut bus = Bus::default();

        let ep_in1 = alloc_ok(&mut bus, UsbDirection::In, Some(1), EndpointType::Interrupt);
        let ep_in2 = EndpointAddress::new(2, UsbDirection::In).unwrap();
        let ep_out1 = alloc_ok(
            &mut bus,
            UsbDirection::Out,
            Some(1),
            EndpointType::Interrupt,
        );
        let ep_out2 = alloc_ok(
            &mut bus,
            UsbDirection::Out,
            Some(2),
            EndpointType::Interrupt,
        );
        let ep_out3 = EndpointAddress::new(3, UsbDirection::Out).unwrap();

        assert!(bus.endpoint_tx(ep_out1).is_some());
        let tx = bus.endpoint_tx(ep_out2).unwrap();

        assert!(bus.endpoint_tx(ep_out3).is_none());
        assert!(bus.endpoint_tx(ep_in1).is_none());
        assert!(bus.endpoint_tx(ep_in2).is_none());

        assert_eq!(bus.impl_poll(), PollResult::None);

        let mut buffer = [0; 1024];
        assert_eq!(bus.impl_read(ep_out1, &mut buffer), Err(Error::WouldBlock));
        assert_eq!(bus.impl_read(ep_out2, &mut buffer), Err(Error::WouldBlock));

        let data = b"testdata";
        tx.send(data.into()).unwrap();

        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0b100,
                ep_in_complete: 0
            }
        );
        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0b100,
                ep_in_complete: 0
            }
        );
        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0b100,
                ep_in_complete: 0
            }
        );

        assert!(tx.try_send(data.into()).is_err());

        assert_eq!(bus.impl_read(ep_out1, &mut buffer), Err(Error::WouldBlock));
        assert_eq!(bus.impl_read(ep_out2, &mut buffer), Ok(data.len()));
        assert_eq!(data, &buffer[..data.len()]);

        assert_eq!(bus.impl_poll(), PollResult::None);

        assert_eq!(bus.impl_read(ep_out1, &mut buffer), Err(Error::WouldBlock));
        assert_eq!(bus.impl_read(ep_out2, &mut buffer), Err(Error::WouldBlock));
        assert!(tx.try_send(data.into()).is_ok());
    }

    #[test]
    fn test_bus_read_in() {
        let mut bus = Bus::default();

        let ep = alloc_ok(&mut bus, UsbDirection::In, Some(1), EndpointType::Interrupt);
        let mut buffer = [0; 1024];
        assert_eq!(bus.impl_read(ep, &mut buffer), Err(Error::InvalidEndpoint));
    }

    #[test]
    fn test_bus_read_unalloc() {
        let bus = Bus::default();

        let ep = EndpointAddress::new(3, UsbDirection::Out).unwrap();
        let mut buffer = [0; 1024];
        assert_eq!(bus.impl_read(ep, &mut buffer), Err(Error::InvalidEndpoint));
    }

    #[test]
    fn test_bus_read_overflow() {
        let mut bus = Bus::default();

        let ep = alloc_ok(
            &mut bus,
            UsbDirection::Out,
            Some(1),
            EndpointType::Interrupt,
        );
        let tx = bus.endpoint_tx(ep).unwrap();
        tx.send(vec![0; 128]).unwrap();

        let mut buffer = [0; 1];
        assert_eq!(bus.impl_read(ep, &mut buffer), Err(Error::BufferOverflow));
        assert_eq!(bus.impl_read(ep, &mut buffer), Err(Error::WouldBlock));
    }

    #[test]
    fn test_bus_read_write() {
        let mut bus = Bus::default();

        let ep_in = alloc_ok(&mut bus, UsbDirection::In, Some(1), EndpointType::Interrupt);
        let ep_out = alloc_ok(
            &mut bus,
            UsbDirection::Out,
            Some(1),
            EndpointType::Interrupt,
        );

        let rx = bus.endpoint_rx(ep_in).unwrap();
        let tx = bus.endpoint_tx(ep_out).unwrap();

        assert_eq!(bus.impl_poll(), PollResult::None);

        let data1 = b"testdata";
        tx.send(data1.into()).unwrap();

        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0b10,
                ep_in_complete: 0
            }
        );
        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0b10,
                ep_in_complete: 0
            }
        );

        let data2 = b"some other important data";
        let result = bus.impl_write(ep_in, data2);
        assert_eq!(result, Ok(data2.len()));

        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0b10,
                ep_in_complete: 0b00
            }
        );
        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0b10,
                ep_in_complete: 0
            }
        );

        let received = rx.recv().unwrap();
        assert_eq!(&received, data2);

        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0b10,
                ep_in_complete: 0b10,
            }
        );
        assert_eq!(
            bus.impl_poll(),
            PollResult::Data {
                ep_out: 0b10,
                ep_in_complete: 0
            }
        );

        let mut buffer = [0; 1024];
        assert_eq!(bus.impl_read(ep_out, &mut buffer), Ok(data1.len()));
        assert_eq!(data1, &buffer[..data1.len()]);

        assert_eq!(bus.impl_poll(), PollResult::None);
    }

    #[test]
    fn test_bus_enable() {
        let mut bus = Bus::default();
        bus.impl_enable();

        let err = alloc_err(&mut bus, UsbDirection::In, None, EndpointType::Interrupt);
        assert_eq!(err, Error::InvalidState);
    }
}
