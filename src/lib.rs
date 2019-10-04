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
//!
//! Note that any given timer can only ever contain one of:
//! * a recurring interval at which to tick. When an interval timeout is set
//! up the first tick will happen one interval's duration after the time at
//! which the timer's timeout was set. (IE the time to first tick is the same
//! as the time between each tick.)
//! * a single timeout which will occur a given duration after the timeout
//! was set.
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
                tv_sec: timeout.as_secs() as libc::time_t,
                tv_nsec: timeout.subsec_nanos() as libc::c_long,
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
                tv_sec: timeout.as_secs() as libc::time_t,
                tv_nsec: timeout.subsec_nanos() as libc::c_long,
            },
            it_value: libc::timespec {
                tv_sec: timeout.as_secs() as libc::time_t,
                tv_nsec: timeout.subsec_nanos() as libc::c_long,
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
            panic!("reading a timerfd should never yield {} bytes", ret);
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

impl Drop for TimerFd {
    fn drop(&mut self) {
        let _ = unsafe { libc::close(self.fd) };
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

    #[test]
    fn deregister_and_drop() {
        let poll = Poll::new().unwrap();
        let mut events = Events::with_capacity(1024);

        let mut timer_one = TimerFd::new(ClockId::Monotonic).unwrap();
        timer_one.set_timeout(&Duration::from_millis(8)).unwrap();
        poll.register(&timer_one, Token(1), Ready::readable(), PollOpt::edge())
            .unwrap();
        let mut timer_two = TimerFd::new(ClockId::Monotonic).unwrap();
        timer_two.set_timeout(&Duration::from_millis(10)).unwrap();
        poll.register(&timer_two, Token(2), Ready::readable(), PollOpt::edge())
            .unwrap();

        // ensure we can deregister and drop a previously
        // registered timer without any issue.
        poll.poll(&mut events, Some(Duration::from_millis(5)))
            .unwrap();
        assert!(events.is_empty());
        timer_one.deregister(&poll).unwrap();
        std::mem::drop(timer_one);

        poll.poll(&mut events, Some(Duration::from_millis(10)))
            .unwrap();
        assert!(!events.is_empty());
        for event in events.iter() {
            match event.token() {
                Token(1) => panic!(),
                Token(2) => {}
                _ => panic!(),
            }
        }
    }

    #[test]
    fn multiple_timers() {
        use std::time::Instant;

        let deadline = Instant::now() + Duration::from_millis(33);
        let mut count_one = 0;
        let mut count_two = 0;
        let mut count_three = 0;
        let mut count_four = 0;

        let poll = Poll::new().unwrap();
        let mut events = Events::with_capacity(1024);

        // timer one should tick once at 10ms
        let mut timer_one = TimerFd::new(ClockId::Monotonic).unwrap();
        timer_one.set_timeout(&Duration::from_millis(10)).unwrap();
        poll.register(&timer_one, Token(1), Ready::readable(), PollOpt::edge())
            .unwrap();

        // timer two should tick each 10ms
        let mut timer_two = TimerFd::new(ClockId::Monotonic).unwrap();
        timer_two
            .set_timeout_interval(&Duration::from_millis(10))
            .unwrap();
        poll.register(&timer_two, Token(2), Ready::readable(), PollOpt::edge())
            .unwrap();

        // timer three should tick once at 20ms
        let mut timer_three = TimerFd::new(ClockId::Monotonic).unwrap();
        timer_three.set_timeout(&Duration::from_millis(20)).unwrap();
        poll.register(&timer_three, Token(3), Ready::readable(), PollOpt::edge())
            .unwrap();

        // timer four should tick each 30ms
        let mut timer_four = TimerFd::new(ClockId::Monotonic).unwrap();
        timer_four
            .set_timeout_interval(&Duration::from_millis(30))
            .unwrap();
        poll.register(&timer_four, Token(4), Ready::readable(), PollOpt::edge())
            .unwrap();

        loop {
            poll.poll(&mut events, Some(deadline - Instant::now()))
                .unwrap();
            if events.is_empty() {
                break;
            }
            for event in events.iter() {
                match event.token() {
                    Token(1) => {
                        let _ = timer_one.read();
                        count_one += 1;
                        if count_one == 1 {
                            assert!(count_two <= 1);
                            assert!(count_three == 0);
                            assert!(count_four == 0);
                            timer_one.set_timeout(&Duration::from_millis(15)).unwrap();
                        }
                    }
                    Token(2) => {
                        let _ = timer_two.read();
                        count_two += 1;
                        assert!(count_two == 1 || count_two == 2);
                        // only let this timer tick twice
                        if count_two >= 2 {
                            timer_two.disarm().unwrap();
                        }
                        // check ticks on other clocks make sense
                        if count_two == 1 {
                            assert!(count_one <= 1);
                            assert!(count_three == 0);
                            assert!(count_four == 0);
                        } else if count_two == 2 {
                            assert!(count_one == 1);
                            assert!(count_three <= 1);
                            assert!(count_four == 0);
                        }
                    }
                    Token(3) => {
                        let _ = timer_three.read();
                        count_three += 1;
                        assert!(count_one == 1);
                        assert!(count_two == 1 || count_two == 2);
                        assert!(count_three == 1);
                        assert!(count_four == 0);
                    }
                    Token(4) => {
                        let _ = timer_four.read();
                        count_four += 1;
                        assert!(count_one == 2);
                        assert!(count_two == 2);
                        assert!(count_three == 1);
                        assert!(count_four == 1);
                    }
                    _ => unreachable!(),
                }
            }
        }

        assert!(count_one == 2);
        assert!(count_two == 2);
        assert!(count_three == 1);
        assert!(count_four == 1);
    }
}
