// pub fn random<T>() -> T
// where
//     rand::distr::StandardUniform: rand::distr::Distribution<T>,
// {
//     rand::random()
// }

pub async fn random() -> u64 {
    rand::random()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        let inner = || async {
            let _x = random().await;
        };

        smol::block_on(inner());
    }
}
