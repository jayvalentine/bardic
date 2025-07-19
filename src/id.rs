use num::{Unsigned, Integer};
use std::collections::HashMap;
use std::hash::Hash;

/// Types implementing this trait can be used as IDs.
/// IDs are required to be integer types so non-conflicting
/// IDs can be easily computed.
/// 
/// This trait is automatically implemented on any type
/// satisfying the constraints.
pub trait IdValue: Unsigned + Integer + Copy + Hash {}
impl<T> IdValue for T where T: Unsigned + Integer + Copy + Hash {}

/// Errors that may occur when creating or referencing an ID.
#[derive(Clone, Copy, Debug)]
pub enum IdError {
    /// The ID being created already exists.
    Duplicate,
    /// The ID being referenced does not exist.
    NonExistent
}

/// A reference to an ID.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct IdRef<T>(T);

/// Manages creation and referencing of IDs.
pub struct IdManager<T: IdValue> {
    next_id_value: T,
    ids: HashMap<String, T>
}

impl<T: IdValue> IdManager<T> {
    /// Construct a new ID manager.
    pub fn new() -> IdManager<T> {
        let next_id_value: T = T::zero();
        let ids = HashMap::new();

        IdManager {
            next_id_value,
            ids
        }
    }

    /// Create a new ID from a string reference.
    /// Operation is successful if the ID does not already exist,
    /// and returns Err if it does.
    /// 
    /// ```
    /// use bardic::id::IdManager;
    /// 
    /// let mut idman = IdManager::<u32>::new();
    /// let id1 = idman.create("foo");
    /// // -> Ok(Id(...))
    /// let id2 = idman.create("foo");
    /// // -> Err
    /// ```
    pub fn create(&mut self, id_str: &str) -> Result<IdRef<T>, IdError> {
        if self.ids.contains_key(id_str) {
            Err(IdError::Duplicate)
        } else {
            let id = IdRef::<T>(self.next_id_value);
            self.ids.insert(id_str.to_string(), self.next_id_value);
            self.next_id_value = self.next_id_value + T::one();
            Ok(id)
        }
    }

    /// Creates a reference to the given ID.
    /// Operation is successful if the ID exists,
    /// and returns Err if it doesn't.
    /// 
    /// # Examples
    /// 
    /// ```
    /// use bardic::id::IdManager;
    /// 
    /// let mut idman = IdManager::<u32>::new();
    /// idman.create("foo");
    /// 
    /// let idref1 = idman.reference("foo");
    /// // -> Ok(IdRef(...))
    /// let idref2 = idman.reference("bar");
    /// // -> Err
    /// ```
    pub fn reference(&self, id_str: &str) -> Result<IdRef<T>, IdError> {
        match self.ids.get(id_str) {
            Some(v) => Ok(IdRef::<T>(*v)),
            None => Err(IdError::NonExistent)
        }
    }
}

impl<T: IdValue> Default for IdManager<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // Tests that ID references can be equality-compared.
    #[test]
    fn test_id_ref_eq() {
        let id = IdRef::<u32>(0);
        let id_ref1 = IdRef::<u32>(0);
        let id_ref2 = IdRef::<u32>(1);

        assert_eq!(id_ref1, id);
        assert_ne!(id_ref2, id);
        assert_ne!(id_ref1, id_ref2)
    }

    // Tests that the ID manager constructs each ID only once.
    #[test]
    fn test_id_manager_create() {
        let mut idman = IdManager::<u64>::new();
        let id1 = idman.create("foo");
        let id2 = idman.create("bar");
        let id3 = idman.create("foo");

        assert!(id1.is_ok());
        assert!(id2.is_ok());
        assert!(id3.is_err());

        assert_ne!(id1.unwrap().0, id2.unwrap().0);
    }
    
    // Tests that the ID manager can create ID references.
    #[test]
    fn test_id_manager_reference() {
        let mut idman = IdManager::<u128>::new();

        let id1 = idman.create("foo").unwrap();
        let id2 = idman.create("bar").unwrap();

        let idref1 = idman.reference("foo").unwrap();
        let idref2 = idman.reference("bar").unwrap();

        assert_eq!(idref1, id1);
        assert_ne!(idref2, id1);

        assert_eq!(idref2, id2);
        assert_eq!(idref1, id1);
    }

    // Tests that IDs and references can be used as hashes.
    #[test]
    fn test_id_hashing() {
        let mut idman = IdManager::<u64>::new();

        let id1 = idman.create("foo").unwrap();
        let id2 = idman.create("bar").unwrap();

        let h: HashMap<IdRef<u64>, String> = HashMap::from([
            (id1, "id1".into()),
            (id2, "id2".into())
        ]);

        let idref1 = idman.reference("foo").unwrap();
        let idref2 = idman.reference("bar").unwrap();

        assert_eq!("id1", h.get(&idref1).unwrap());
        assert_eq!("id2", h.get(&idref2).unwrap());
    }
}
