/// Types implementing this trait can be used as IDs for entities.
/// This trait is automatically implemented for all types implementing
/// the bounds.
pub trait IdType: Eq {}
impl<T> IdType for T where T: Eq {}

/// A trait for entities in an entity-action system.
/// 
/// Provides methods for accessing the internal state of an entity.
pub trait Entity<ID: IdType, T> {
    /// A unique identifier for this entity.
    fn id(&self) -> &ID;

    /// Does this entity have the given tag?
    fn has_tag(&self, t: &T) -> bool;

    /// What actions can this entity take in the given world state?
    /// 
    /// Actions are weighted to indicate likelihood of the entity
    /// taking that action.
    fn possible_actions(&self, s: &WorldState<ID>) -> Vec<(u32, Action)>;
}

/// A relationship between two entities.
pub struct Relationship<ID: IdType> {
    subject: ID,
    object: ID,
    kind: RelationshipKind
}

/// Represents the possible kinds of relationship between entities.
#[derive(PartialEq, Eq, Debug)]
pub enum RelationshipKind {
    /// The relationship describes the subject's position relative to the object.
    /// The string describes the kind of positioning, e.g. "on", "in", "near to".
    Location(String)
}

/// A collection of [Relationship]s representing the current external state
/// of all entities in the system.
pub struct WorldState<ID: IdType> {
    relationships: Vec<Relationship<ID>>
}

impl<ID: IdType> WorldState<ID> {
    /// Create an empty world state.
    pub fn new() -> Self {
        WorldState {
            relationships: Vec::new()
        }
    }

    /// Add a relationship to this world state.
    pub fn add_relationship(&mut self, r: Relationship<ID>) {
        self.relationships.push(r)
    }

    /// Get all relationships that reference the given entity
    /// as a subject.
    pub fn with_subject<'a, T, E: Entity<ID, T>>(&'a self, e: &'a E) -> impl Iterator<Item = &'a Relationship<ID>> {
        self.relationships.iter().filter(|r| {
            r.subject.eq(e.id())
        })
    }
}

/// An action that may be taken by an entity.
pub struct Action {

}

#[cfg(test)]
mod tests {
    use super::*;

    struct TestEntity {
        id: u32
    }

    impl Entity<u32, u32> for TestEntity {
        fn id(&self) -> &u32 {
            &self.id
        }

        fn has_tag(&self, t: &u32) -> bool {
            false
        }

        fn possible_actions(&self, s: &WorldState<u32>) -> Vec<(u32, Action)> {
            Vec::new()
        }
    }

    /// Tests that relationships in a world state can be filtered
    /// based on subject.
    #[test]
    fn test_filter_by_subject() {
        let mut w = WorldState::<u32>::new();

        let e1 = TestEntity { id: 1 };
        let e2 = TestEntity { id: 2 };
        let e3 = TestEntity { id: 3 };

        w.add_relationship(Relationship { subject: e1.id, object: e3.id, kind: RelationshipKind::Location("in".into()) });
        w.add_relationship(Relationship { subject: e2.id, object: e3.id, kind: RelationshipKind::Location("in".into()) });
        w.add_relationship(Relationship { subject: e2.id, object: e1.id, kind: RelationshipKind::Location("near".into()) });

        assert_eq!(1, w.with_subject(&e1).count());
        assert_eq!(1, w.with_subject(&e1).next().unwrap().subject);
        assert_eq!(3, w.with_subject(&e1).next().unwrap().object);
        assert_eq!(RelationshipKind::Location("in".into()), w.with_subject(&e1).next().unwrap().kind);
    }
}
