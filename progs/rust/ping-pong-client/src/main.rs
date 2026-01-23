use anyhow::Result;
use async_channel::Sender;
use std::net::TcpStream;
use std::time::Duration;

use futures::FutureExt;
use futures::pin_mut;

use smol::{Async, Timer, fs};
use std::path::Path;

async fn client<P: AsRef<Path>>(path: P) -> Result<()> {
    use smol::io::AsyncWriteExt;

    let file_contents = fs::read(path).await?;

    let mut stream = Async::<TcpStream>::connect(([127, 0, 0, 1], 6000)).await?;

    for bytes in file_contents.chunks(16) {
        Timer::after(Duration::from_millis(50)).await;
        stream.write_all(bytes).await?;
    }

    Ok(())
}

async fn check_server(cancel: Sender<()>) -> Result<()> {
    use futures::io::{AsyncReadExt, AsyncWriteExt};

    let mut stream = Async::<TcpStream>::connect(([127, 0, 0, 1], 6001)).await?;
    let mut buf = vec![0; 16];

    loop {
        Timer::after(Duration::from_secs(1)).await;
        stream.write_all(b"PING\n").await?;

        let ack = stream.read(&mut buf).fuse();
        let timer = Timer::after(Duration::from_secs(2)).fuse();

        pin_mut!(ack, timer);

        futures::select! {
            r = ack => {
                println!("{r:?}");
            }
            _ = timer => {
                return cancel.send(()).await.map_err(|_| {
                    anyhow::anyhow!("Failed to send cancel signal")
                });
            }
        }
    }
}

async fn send_all() -> Result<()> {
    use smol::stream::StreamExt;

    let mut entries = fs::read_dir("./assets/").await?;
    let mut tasks = vec![];

    while let Some(entry) = entries.try_next().await? {
        tasks.push(smol::spawn(client(entry.path())));
    }

    for task in tasks {
        task.await?;
    }

    Ok(())
}

fn main() -> Result<()> {
    smol::block_on(async {
        let (snd, recv) = async_channel::unbounded();
        smol::spawn(check_server(snd.clone())).detach();

        let send_it_all = send_all().fuse();
        let cancelled = recv.recv().fuse();
        pin_mut!(send_it_all, cancelled);

        futures::select! {
            res = send_it_all => res,
            _ = cancelled => {
                anyhow::bail!("Server failed to respond, quiting")
            },
        }
    })
}
