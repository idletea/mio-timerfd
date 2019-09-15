//! # mio-timerfd
//!
//! A linux timerfd wrapper for mio, making it fairly simple to integrate
//! timers into mio-based systems with minimal overhead. Reading timerfd(7)
//! is recommended for using this library, though for simple use all you
//! really need to know is:
//!
//! ```rust
//! # use std::time::Duration;
//! # use mio_timerfd::*;
//! # use mio::*;
//! let mut timer = TimerFd::new(ClockId::Monotonic).unwrap();
//! timer.set_timeout(&Duration::from_millis(10)).unwrap();
//!
//! let poll = Poll::new().unwrap();
//! let mut events = Events::with_capacity(64);
//! poll.register(&timer, Token(0), Ready::readable(), PollOpt::edge()).unwrap();
//!
//! // will wait for 10ms to pass
//! poll.poll(&mut events, None).unwrap();
//! // always call `read` after the timerfd wakes your thread up, or
//! // else the readability of the fd isn't going to change and therefore
//! // the next call to poll will either wake immediately if level triggered,
//! // or never wake for the timerfd again if edge triggered.
//! let number_of_timeouts = timer.read().unwrap();
//! # assert!(number_of_timeouts == 1);
//! ```
use libc::{c_int, c_void};
use mio::unix::EventedFd;
use mio::{Evented, Poll, PollOpt, Ready, Token};
use std::io;
use std::mem::MaybeUninit;
use std::os::unix::io::{AsRawFd, RawFd};
use std::time::Duration;

#[cfg(not(target_os = "linux"))]
compile_error!("timerfd is a linux specific feature");

//
//
// TimerFd
//
//

/// A timerfd which can be used to create mio-compatible
/// timers on linux targets.
pub struct TimerFd {
    fd: c_int,
}

impl TimerFd {
    /// Create a new timerfd using the given clock; if you're not sure
    /// what clock to use read timerfd(7) for more details, or know
    /// that `ClockId::Monotonic` is a good default for most programs.
    pub fn new(clockid: ClockId) -> io::Result<Self> {
        let flags = libc::TFD_NONBLOCK | libc::TFD_CLOEXEC;
        Self::create(clockid.into(), flags)
    }

    /// Set a single timeout to occur after the specified duration.
    pub fn set_timeout(&mut self, timeout: &Duration) -> io::Result<()> {
        // this is overflow safe unless the timoeout is > ~292 billion years.
        let new_value = libc::itimerspec {
            it_interval: libc::timespec {
                tv_sec: 0,
                tv_nsec: 0,
            },
            it_value: libc::timespec {
                tv_sec: timeout.as_secs() as i64,
                tv_nsec: i64::from(timeout.subsec_nanos()),
            },
        };
        self.settime(0, &new_value).map(|_old_value| ())
    }

    /// Set a timeout to occur at each interval of the
    /// specified duration from this point in time forward.
    pub fn set_timeout_interval(&mut self, timeout: &Duration) -> io::Result<()> {
        // this is overflow safe unless the timoeout is > ~292 billion years.
        let new_value = libc::itimerspec {
            it_interval: libc::timespec {
                tv_sec: timeout.as_secs() as i64,
                tv_nsec: i64::from(timeout.subsec_nanos()),
            },
            it_value: libc::timespec {
                tv_sec: timeout.as_secs() as i64,
                tv_nsec: i64::from(timeout.subsec_nanos()),
            },
        };
        self.settime(0, &new_value).map(|_old_value| ())
    }

    /// Unset any existing timeouts on the timer,
    /// making this timerfd inert until rearmed.
    pub fn disarm(&mut self) -> io::Result<()> {
        self.set_timeout(&Duration::from_secs(0))
    }

    /// Read the timerfd to reset the readability of the timerfd,
    /// and allow determining how many times the timer has elapsed
    /// since the last read. This should usually be read after
    /// any wakeups caused by this timerfd, as reading the timerfd
    /// is important to reset the readability of the timerfd.
    ///
    /// Failing to call this after this timerfd causes a wakeup
    /// will result in immediately re-waking on this timerfd if
    /// level polling, or never re-waking if edge polling.
    pub fn read(&self) -> io::Result<u64> {
        let mut buf = [0u8; 8];
        let ret = unsafe { libc::read(self.fd, buf.as_mut_ptr() as *mut c_void, buf.len()) };
        if ret == 8 {
            Ok(u64::from_ne_bytes(buf))
        } else if ret == -1 {
            let errno = unsafe { *libc::__errno_location() };
            if errno == libc::EAGAIN {
                Ok(0)
            } else {
                Err(io::Error::from_raw_os_error(errno))
            }
        } else {
            panic!("reading a timerfd and encountered end of file");
        }
    }

    /// Wrapper of `timerfd_create` from timerfd_create(7); For
    /// most users it's probably easier to use the `TimerFd::new`.
    ///
    /// Note that this library may cause the thread to block when
    /// `TimerFd::read` is called if the `TFD_NONBLOCK` flag is
    /// not included in the flags.
    pub fn create(clockid: c_int, flags: c_int) -> io::Result<Self> {
        let fd = unsafe { libc::timerfd_create(clockid, flags) };
        if fd == -1 {
            Err(io::Error::last_os_error())
        } else {
            Ok(Self { fd })
        }
    }

    /// Wrapper of `timerfd_settime` from timerfd_create(7); For most
    /// users it's probably easier to use the `TimerFd::set_timeout` or
    /// the `TimerFd::set_timeout_interval` functions.
    pub fn settime(
        &mut self,
        flags: c_int,
        new_value: &libc::itimerspec,
    ) -> io::Result<libc::itimerspec> {
        let mut old_spec_mem = MaybeUninit::<libc::itimerspec>::uninit();
        let ret =
            unsafe { libc::timerfd_settime(self.fd, flags, new_value, old_spec_mem.as_mut_ptr()) };
        if ret == -1 {
            Err(io::Error::last_os_error())
        } else {
            let old_spec = unsafe { old_spec_mem.assume_init() };
            Ok(old_spec)
        }
    }

    /// Wrapper of `timerfd_gettime` from timerfd_create(7)
    pub fn gettime(&self) -> io::Result<libc::itimerspec> {
        let mut old_spec_mem = MaybeUninit::<libc::itimerspec>::uninit();
        let ret = unsafe { libc::timerfd_gettime(self.fd, old_spec_mem.as_mut_ptr()) };
        if ret == -1 {
            Err(io::Error::last_os_error())
        } else {
            let old_spec = unsafe { old_spec_mem.assume_init() };
            Ok(old_spec)
        }
    }
}

impl AsRawFd for TimerFd {
    fn as_raw_fd(&self) -> RawFd {
        self.fd
    }
}

impl Evented for TimerFd {
    fn register(
        &self,
        poll: &Poll,
        token: Token,
        interest: Ready,
        opts: PollOpt,
    ) -> io::Result<()> {
        EventedFd(&self.fd).register(poll, token, interest, opts)
    }

    fn reregister(
        &self,
        poll: &Poll,
        token: Token,
        interest: Ready,
        opts: PollOpt,
    ) -> io::Result<()> {
        EventedFd(&self.fd).reregister(poll, token, interest, opts)
    }

    fn deregister(&self, poll: &Poll) -> io::Result<()> {
        EventedFd(&self.fd).deregister(poll)
    }
}

//
//
// ClockId
//
//

/// Clock used to mark the progress of the timer. timerfd_create(7)
#[derive(Copy, Clone)]
pub enum ClockId {
    RealTime,
    Monotonic,
    BootTime,
    RealTimeAlarm,
    BootTimeAlarm,
}

impl Into<c_int> for ClockId {
    fn into(self) -> c_int {
        match self {
            ClockId::RealTime => libc::CLOCK_REALTIME,
            ClockId::Monotonic => libc::CLOCK_MONOTONIC,
            ClockId::BootTime => libc::CLOCK_BOOTTIME,
            ClockId::RealTimeAlarm => libc::CLOCK_REALTIME_ALARM,
            ClockId::BootTimeAlarm => libc::CLOCK_BOOTTIME_ALARM,
        }
    }
}

//
//
// Testing
//
//

#[cfg(test)]
mod test {
    use super::*;
    use mio::Events;

    const TOK: Token = Token(0);
    const TIMEOUT: Duration = Duration::from_millis(6);

    #[test]
    fn single_timeout() {
        let poll = Poll::new().unwrap();
        let mut events = Events::with_capacity(1024);
        let mut timer = TimerFd::new(ClockId::Monotonic).unwrap();
        timer.set_timeout(&TIMEOUT).unwrap();
        poll.register(&timer, TOK, Ready::readable(), PollOpt::edge())
            .unwrap();

        // timer should not elapse before the timeout
        poll.poll(&mut events, Some(TIMEOUT / 2)).unwrap();
        assert!(events.is_empty());
        assert!(timer.read().unwrap() == 0);

        // timer should elapse after its timeout has passed
        poll.poll(&mut events, Some(TIMEOUT)).unwrap();
        assert!(!events.is_empty());
        assert!(timer.read().unwrap() == 1);

        // timer should not elapse again without a rearm
        poll.poll(&mut events, Some(TIMEOUT)).unwrap();
        assert!(events.is_empty());
        assert!(timer.read().unwrap() == 0);
    }

    #[test]
    fn disarm_rearm_single_timeout() {
        let poll = Poll::new().unwrap();
        let mut events = Events::with_capacity(1024);
        let mut timer = TimerFd::new(ClockId::Monotonic).unwrap();
        timer.set_timeout(&TIMEOUT).unwrap();
        poll.register(&timer, TOK, Ready::readable(), PollOpt::edge())
            .unwrap();

        // timer should not elapse before the timeout
        poll.poll(&mut events, Some(TIMEOUT / 2)).unwrap();
        assert!(events.is_empty());
        assert!(timer.read().unwrap() == 0);

        // timer should not elapse after its first
        // timeout has passed if we disarm the timer.
        timer.disarm().unwrap();
        poll.poll(&mut events, Some(TIMEOUT)).unwrap();
        assert!(events.is_empty());
        assert!(timer.read().unwrap() == 0);

        // timer should elapse after the rearmed timeout
        timer.set_timeout(&TIMEOUT).unwrap();
        poll.poll(&mut events, Some(TIMEOUT * 2)).unwrap();
        assert!(!events.is_empty());
        assert!(timer.read().unwrap() == 1);
    }

    #[test]
    fn timeout_interval() {
        let poll = Poll::new().unwrap();
        let mut events = Events::with_capacity(1024);
        let mut timer = TimerFd::new(ClockId::Monotonic).unwrap();
        timer.set_timeout_interval(&TIMEOUT).unwrap();
        poll.register(&timer, TOK, Ready::readable(), PollOpt::edge())
            .unwrap();

        // timer should not elapse before the timeout
        poll.poll(&mut events, Some(TIMEOUT / 2)).unwrap();
        assert!(events.is_empty());
        assert!(timer.read().unwrap() == 0);

        // timer should elapsed after its timeout
        poll.poll(&mut events, Some(TIMEOUT)).unwrap();
        assert!(!events.is_empty());
        assert!(timer.read().unwrap() == 1);

        // timer should elapse again after another timeout
        poll.poll(&mut events, Some(TIMEOUT * 2)).unwrap();
        assert!(!events.is_empty());
        assert!(timer.read().unwrap() == 1);
    }

    #[test]
    fn disarm_rearm_timeout_interval() {
        let poll = Poll::new().unwrap();
        let mut events = Events::with_capacity(1024);
        let mut timer = TimerFd::new(ClockId::Monotonic).unwrap();
        timer.set_timeout_interval(&TIMEOUT).unwrap();
        poll.register(&timer, TOK, Ready::readable(), PollOpt::edge())
            .unwrap();

        // timer should not elapse before the timeout
        poll.poll(&mut events, Some(TIMEOUT / 2)).unwrap();
        assert!(events.is_empty());
        assert!(timer.read().unwrap() == 0);

        // timer should not elapse after its first
        // timeout has passed if we disarm the timer,
        timer.disarm().unwrap();
        poll.poll(&mut events, Some(TIMEOUT)).unwrap();
        assert!(events.is_empty());
        assert!(timer.read().unwrap() == 0);

        // timer should elapse after the rearmed timeout
        timer.set_timeout_interval(&TIMEOUT).unwrap();
        poll.poll(&mut events, Some(TIMEOUT + (TIMEOUT / 2)))
            .unwrap();
        assert!(!events.is_empty());
        assert!(timer.read().unwrap() == 1);

        // timer should elapse after the rearmed timeout
        timer.set_timeout_interval(&TIMEOUT).unwrap();
        poll.poll(&mut events, Some(TIMEOUT + (TIMEOUT / 2)))
            .unwrap();
        assert!(!events.is_empty());
        assert!(timer.read().unwrap() == 1);
    }
}
