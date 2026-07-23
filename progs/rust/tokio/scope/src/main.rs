//Scope: program
use std::{
    fmt::Display,
    sync::atomic::{AtomicUsize, Ordering},
    time::Duration,
};
use tokio::time::sleep;

static COUNTER: AtomicUsize = AtomicUsize::new(0);

async fn write<T: AsRef<str> + Display + Sized>(msg: T) {
    println!("{}", msg);
    sleep(Duration::from_millis(5)).await;
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
    tokio::spawn(inner());

    0
}

#[tokio::main]
async fn main() {
    let a = async_int();
    let b = async_int();

    println!("working");

    let c = a.await + b.await;

    write(c.to_string()).await;
    write("exiting").await;
}
