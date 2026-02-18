use std::collections::HashMap;
use std::net::{SocketAddr, TcpListener, TcpStream};

use async_channel::{Receiver, Sender, bounded};
use async_dup::Arc;
use smol::{Async, future, io, prelude::*};

/// An event on the chat server.
enum Event {
    Join(SocketAddr),
    Message(SocketAddr, String),
    Leave(SocketAddr),
}

async fn dispatch(receiver: Receiver<Event>) -> io::Result<()> {
    let mut map = HashMap::<SocketAddr, String>::new();

    while let Ok(event) = receiver.recv().await {
        match event {
            Event::Join(addr) => {
                map.insert(addr, String::new());
                eprintln!("{} has joined\n", addr);
            }
            Event::Leave(addr) => {
                let text = map.remove(&addr);
                drop(text); // Flush to disk
                eprintln!("{} has left\n", addr);
            }
            Event::Message(addr, msg) => {
                eprintln!("Received {addr} from {msg}");
                map.entry(addr).and_modify(|v| {
                    v.push_str(&msg);
                });
            }
        }
    }
    Ok(())
}

async fn read_messages(sender: Sender<Event>, client: Arc<Async<TcpStream>>) -> io::Result<()> {
    let addr = client.get_ref().peer_addr()?;
    let mut lines = io::BufReader::new(client).lines();

    while let Some(line) = lines.next().await {
        let line = line?;
        sender.send(Event::Message(addr, line)).await.ok();
    }
    Ok(())
}

async fn server() -> io::Result<()> {
    let listener = Async::<TcpListener>::bind(([127, 0, 0, 1], 6000))?;

    println!("Listening on {}", listener.get_ref().local_addr()?);

    let (sender, receiver) = bounded(100);
    smol::spawn(dispatch(receiver)).detach();

    loop {
        let (stream, addr) = listener.accept().await?;
        let client = Arc::new(stream);
        let sender = sender.clone();

        smol::spawn(async move {
            sender.send(Event::Join(addr)).await.ok();
            read_messages(sender.clone(), client).await.ok();
            sender.send(Event::Leave(addr)).await.ok();
        })
        .detach();
    }
}

async fn monitor() -> io::Result<()> {
    use async_dup::Mutex;
    use rand::{Rng, SeedableRng, rngs::StdRng};
    use smol::Timer;

    let listener = Async::<TcpListener>::bind(([127, 0, 0, 1], 6001))?;
    let rng = Arc::new(Mutex::new(StdRng::from_os_rng()));

    loop {
        let (mut stream, _) = listener.accept().await?;

        let rng = Arc::clone(&rng);
        smol::spawn(async move {
            let mut buffer = [0; 64];
            let n = stream.read(&mut buffer).await.unwrap();
            let message = String::from_utf8_lossy(&buffer[..n]);

            let mut locked_rng = rng.lock();
            let to_wait = locked_rng.random_range(0..=6);
            eprintln!("Heartbeat {message} waiting {to_wait}");
            Timer::after(std::time::Duration::from_secs(to_wait)).await;
            stream.write_all(b"PONG\n").await.unwrap();
        })
        .detach()
    }
}

fn main() -> io::Result<()> {
    smol::block_on(async {
        future::try_zip(server(), monitor()).await?;

        Ok(())
    })
}
