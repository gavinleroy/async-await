use std::{
    pin::Pin,
    task::{Context, Poll},
};

use tokio::time::Sleep;

struct Work {
    state: WorkState,
}

enum WorkState {
    Created,
    Sleeping(Pin<Box<Sleep>>),
    Terminated,
}

impl Future for Work {
    type Output = ();

    fn poll(mut self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
        match &mut self.state {
            WorkState::Created => {
                let fut = tokio::time::sleep(std::time::Duration::from_secs(60));
                self.state = WorkState::Sleeping(Box::pin(fut));
                Poll::Pending
            }
            WorkState::Sleeping(fut) => match fut.as_mut().poll(cx) {
                Poll::Ready(()) => {
                    println!("did some work");
                    self.state = WorkState::Terminated;
                    Poll::Ready(())
                }
                Poll::Pending => Poll::Pending,
            },
            WorkState::Terminated => panic!("polled after completion"),
        }
    }
}

impl Drop for Work {
    fn drop(&mut self) {
        println!("sneaky work");
    }
}

fn work() -> Work {
    Work {
        state: WorkState::Created,
    }
}

// async fn work() {
//     tokio::time::sleep(std::time::Duration::from_secs(60)).await;
//     println!("did some work");
// }

#[tokio::main]
async fn main() {
    let t = tokio::spawn(work());
    tokio::time::sleep(std::time::Duration::from_secs(1)).await;
    t.abort();
    tokio::time::sleep(std::time::Duration::from_secs(1)).await;
}

/* ======= */
/* THREADS */
/* ======= */

// use std::sync::mpsc::{self, Receiver};
// use std::thread;
// use std::time::Duration;
//
// fn heartbeat(cancel: Receiver<()>) {
//     while cancel.try_recv().is_err() {
//         thread::sleep(Duration::from_millis(1));
//         println!("did some work");
//     }
//     println!("exiting");
// }
//
// fn main() {
//     let (tx, rx) = mpsc::channel();
//     thread::spawn(move || heartbeat(rx));
//
//     thread::sleep(Duration::from_millis(10));
//     tx.send(()).unwrap();
//     thread::sleep(Duration::from_millis(10));
//
//     println!("done");
// }
