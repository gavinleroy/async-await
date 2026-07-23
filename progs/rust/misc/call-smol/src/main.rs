use std::path::Path;

type Result<T> = std::result::Result<T, std::io::Error>;

async fn read_file<P: AsRef<Path>>(file: P) -> Result<String> {
    smol::fs::read_to_string(file).await
}

async fn lines(file: &str) -> Result<usize> {
    let contents = read_file(file).await?;
    Ok(contents.lines().count())
}

const FILE: &str = "../../assets/shakespeare.txt";

fn main() {
    smol::block_on(async {
        let timer = std::time::Instant::now();
        let n = lines(FILE).await.unwrap();
        assert_eq!(n, 65019);
        println!("done {}μs", timer.elapsed().as_micros());
    })
}
