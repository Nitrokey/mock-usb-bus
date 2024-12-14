// SPDX-FileCopyrightText: Robin Krahl <robin.krahl@ireas.org>
// SPDX-License-Identifier: Apache-2.0 or MIT

use usb_device03::{
    bus::{PollResult, UsbBus},
    endpoint::{EndpointAddress, EndpointType},
    UsbDirection, UsbError,
};

use crate::{Bus, Error};

impl UsbBus for Bus {
    fn alloc_ep(
        &mut self,
        ep_dir: UsbDirection,
        ep_addr: Option<EndpointAddress>,
        ep_type: EndpointType,
        _max_packet_size: u16,
        _interval: u8,
    ) -> Result<EndpointAddress, UsbError> {
        self.impl_alloc_ep(ep_dir.into(), ep_addr.map(From::from), ep_type.into())
            .map(From::from)
            .map_err(From::from)
    }

    fn enable(&mut self) {
        self.impl_enable()
    }

    fn reset(&self) {
        unimplemented!("reset");
    }

    fn set_device_address(&self, _addr: u8) {
        unimplemented!("set_device_address");
    }

    fn write(&self, ep_addr: EndpointAddress, buf: &[u8]) -> Result<usize, UsbError> {
        self.impl_write(ep_addr.into(), buf).map_err(From::from)
    }

    fn read(&self, ep_addr: EndpointAddress, buf: &mut [u8]) -> Result<usize, UsbError> {
        self.impl_read(ep_addr.into(), buf).map_err(From::from)
    }

    fn set_stalled(&self, _ep_addr: EndpointAddress, _stalled: bool) {
        unimplemented!("set_stalled");
    }

    fn is_stalled(&self, _ep_addr: EndpointAddress) -> bool {
        unimplemented!("is_stalled");
    }

    fn suspend(&self) {
        unimplemented!("suspend");
    }

    fn resume(&self) {
        unimplemented!("resume");
    }

    fn poll(&self) -> PollResult {
        self.impl_poll().into()
    }
}

impl From<UsbDirection> for crate::UsbDirection {
    fn from(direction: UsbDirection) -> Self {
        match direction {
            UsbDirection::In => Self::In,
            UsbDirection::Out => Self::Out,
        }
    }
}

impl From<crate::UsbDirection> for UsbDirection {
    fn from(direction: crate::UsbDirection) -> Self {
        match direction {
            crate::UsbDirection::In => Self::In,
            crate::UsbDirection::Out => Self::Out,
        }
    }
}

impl From<EndpointAddress> for crate::EndpointAddress {
    fn from(address: EndpointAddress) -> Self {
        Self::new(address.index() as _, address.direction().into()).unwrap()
    }
}

impl From<crate::EndpointAddress> for EndpointAddress {
    fn from(address: crate::EndpointAddress) -> Self {
        Self::from_parts(address.index().into(), address.direction().into())
    }
}

impl From<EndpointType> for crate::EndpointType {
    fn from(ty: EndpointType) -> Self {
        match ty {
            EndpointType::Control => Self::Control,
            EndpointType::Isochronous { .. } => Self::Isochronous,
            EndpointType::Bulk => Self::Bulk,
            EndpointType::Interrupt => Self::Interrupt,
        }
    }
}

impl From<Error> for UsbError {
    fn from(error: Error) -> Self {
        match error {
            Error::BufferOverflow => Self::BufferOverflow,
            Error::EndpointOverflow => Self::EndpointOverflow,
            Error::InvalidEndpoint => Self::InvalidEndpoint,
            Error::InvalidState => Self::InvalidState,
            Error::WouldBlock => Self::WouldBlock,
        }
    }
}

impl From<crate::PollResult> for PollResult {
    fn from(result: crate::PollResult) -> Self {
        match result {
            crate::PollResult::Data {
                ep_out,
                ep_in_complete,
            } => PollResult::Data {
                ep_out,
                ep_in_complete,
                ep_setup: 0,
            },
            crate::PollResult::None => PollResult::None,
        }
    }
}
