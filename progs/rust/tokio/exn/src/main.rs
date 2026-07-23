//Exn: awaited (for results, panics are just logged)
use std::{fmt::Display, time::Duration};

use tokio::time::sleep;

async fn write<T: AsRef<str> + Display + Sized>(msg: T) {
    println!("{}", msg);
    sleep(Duration::from_millis(5)).await
}

async fn async_int() -> i32 {
    let inner = async || panic!("argh");
    let _ = tokio::spawn(inner());
    0
}

#[tokio::main]
async fn main() {
    let a = async_int();
    let b = async_int();
    println!("working");
    let c = a.await + b.await;
    write(c.to_string()).await;
}
