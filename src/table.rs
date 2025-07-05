use rand::Rng;

pub struct RollTable<T> {
    items: Vec<T>
}

/// A table of items that can be randomly sampled from.
impl<T> RollTable<T> {
    // Create a new rolltable with the given set of items.
    pub fn new(items: Vec<T>) -> RollTable<T> {
        RollTable { items }
    }

    /// Return a random item from this table.
    pub fn roll<R: Rng>(&self, rng: &mut R) -> &T {
        let i = rng.random_range(0..self.items.len());
        self.items.get(i).unwrap()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rolltable() {
        let t = RollTable::new(vec![42]);
        let mut rng = rand::rng();

        assert_eq!(42, *t.roll(&mut rng));
    }
}
