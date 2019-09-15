# mio-timerfd

A [mio](https://crates.io/crates/mio) wrapper for linux's [timerfd](http://man7.org/linux/man-pages/man2/timerfd_create.2.html) feature. For linux-specific software this is likely the easiest (and probably most performant, but I'm not benchmarking) way to get asynchronous timers into your code.
