// Figure 4 (Eagerness): Rust is LAZY — calling an async fn constructs a
// future and runs none of its body until the future is awaited.
// Expected output: C A B (deterministic).

async fn work(msg: &str) {
    println!("{msg}");
}

#[tokio::main]
async fn main() {
    let a = work("A");
    let b = work("B");
    println!("C");
    a.await;
    b.await;
}
