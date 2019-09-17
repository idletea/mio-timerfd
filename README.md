# mio-timerfd

[![crates.io](https://img.shields.io/crates/v/mio-timerfd?style=for-the-badge)](https://crates.io/crates/mio-timerfd) [![license](https://img.shields.io/crates/l/mio-timerfd?style=for-the-badge)](https://docs.rs/mio-timerfd)

A [mio](https://crates.io/crates/mio) wrapper for linux's [timerfd](http://man7.org/linux/man-pages/man2/timerfd_create.2.html) feature. For linux-specific software this is likely the easiest (and probably most performant, but I'm not benchmarking) way to get asynchronous timers into your code.

# simple example

```rust
let poll = Poll::new().unwrap();
let mut events = Events::with_capacity(1024);
let mut timer = TimerFd::new(ClockId::Monotonic).unwrap();
timer.set_timeout_interval(&Duration::from_millis(10)).unwrap();
poll.register(&timer, Token(0), Ready::readable(), PollOpt::edge())
	.unwrap();

// effectively sleeps the thread for 10ms
poll.poll(&mut events, None).unwrap();
assert!(timer.read().unwrap() == 1);
```
