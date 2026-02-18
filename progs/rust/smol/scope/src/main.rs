//Scope: region
use std::{
    fmt::Display,
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};

static COUNTER: AtomicUsize = AtomicUsize::new(0);

async fn write<T: AsRef<str> + Display + Sized>(msg: T) {
    println!("{}", msg);
    smol::Timer::after(Duration::from_millis(5)).await;
}

async fn async_int() -> i32 {
    let inner = async || {
        let me = COUNTER.fetch_add(1, Ordering::SeqCst);
        let until = rand::random_range(0..50);

        for _ in 0..until {
            write(format!("{me} waiting")).await;
        }
        write(format!("{me} done")).await;

        until
    };
    // NOTE, region scoped because the Drop implementation for
    // Tasks in SMOL is that they cancel rather than detach
    let _ = smol::spawn(inner());

    0
}

fn main() {
    smol::block_on(async {
        let a = async_int();
        let b = async_int();

        println!("working");

        let c = a.await + b.await;

        write(c.to_string()).await;
        write("exiting").await;
    })
}
