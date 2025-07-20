use std::{collections::HashSet, hash::Hash};

/// Types implementing this trait can be used as IDs for entities.
/// This trait is automatically implemented for all types implementing
/// the bounds.
pub trait IdType: Eq + Hash {}
impl<T> IdType for T where T: Eq + Hash {}

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
    fn possible_actions(&self, s: &WorldState<ID>) -> Vec<(u32, Action<ID>)>;
}

/// A relationship between two entities.
#[derive(PartialEq, Eq, Hash)]
pub struct Relationship<ID: IdType> {
    subject: ID,
    object: ID,
    kind: RelationshipKind
}

/// Represents the possible kinds of relationship between entities.
#[derive(PartialEq, Eq, Hash, Debug)]
pub enum RelationshipKind {
    /// The relationship describes the subject's position relative to the object.
    /// The string describes the kind of positioning, e.g. "on", "in", "near to".
    Location(String)
}

/// A collection of [Relationship]s representing the current external state
/// of all entities in the system.
pub struct WorldState<ID: IdType> {
    relationships: HashSet<Relationship<ID>>
}

impl<ID: IdType> WorldState<ID> {
    /// Create an empty world state.
    pub fn new() -> Self {
        WorldState {
            relationships: HashSet::new()
        }
    }

    /// Add a relationship to this world state.
    pub fn add_relationship(&mut self, r: Relationship<ID>) {
        self.relationships.insert(r);
    }

    /// Get all relationships that reference the given entity
    /// as a subject.
    pub fn with_subject<'a, T, E: Entity<ID, T>>(&'a self, e: &'a E) -> impl Iterator<Item = &'a Relationship<ID>> {
        self.relationships.iter().filter(|r| {
            r.subject.eq(e.id())
        })
    }

    /// Apply the given action to this world state.
    pub fn apply_action(&mut self, a: Action<ID>) {
        for r in a.removed_relationships {
            self.relationships.remove(&r);
        }
        for r in a.added_relationships {
            self.relationships.insert(r);
        }
    }
}

/// An action that may be taken by an entity.
pub struct Action<ID: IdType> {
    removed_relationships: HashSet<Relationship<ID>>,
    added_relationships: HashSet<Relationship<ID>>
}

impl<'a, ID: IdType> Action<ID> {
    fn new(removed_relationships: HashSet<Relationship<ID>>, added_relationships: HashSet<Relationship<ID>>) -> Action<ID>
    {
        Action {
            removed_relationships,
            added_relationships
        }
    }
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

        fn possible_actions(&self, s: &WorldState<u32>) -> Vec<(u32, Action<u32>)> {
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

    /// Tests that actions can both remove and add relationships to the world state.
    #[test]
    fn test_apply_action() {
        let mut w = WorldState::<u32>::new();

        w.add_relationship(Relationship { subject: 0, object: 1, kind: RelationshipKind::Location("near".into()) });
        w.add_relationship(Relationship { subject: 0, object: 2, kind: RelationshipKind::Location("in".into()) });
        w.add_relationship(Relationship { subject: 1, object: 2, kind: RelationshipKind::Location("in".into()) });

        let removed = HashSet::from([Relationship { subject: 0, object: 1, kind:RelationshipKind::Location("near".into())}]);
        let added = HashSet::from([Relationship { subject: 0, object: 1, kind:RelationshipKind::Location("on".into())}]);
        let a = Action::new(removed, added);

        w.apply_action(a);

        assert_eq!(3, w.relationships.len());

        // Check that the unaffected relationships remain in the set.
        assert!(w.relationships.contains(&Relationship { subject: 0, object: 2, kind: RelationshipKind::Location("in".into()) }));
        assert!(w.relationships.contains(&Relationship { subject: 1, object: 2, kind: RelationshipKind::Location("in".into()) }));

        // Check that the new relationship has been added.
        assert!(w.relationships.contains(&Relationship { subject: 0, object: 1, kind: RelationshipKind::Location("on".into()) }));

        // Check that the old relationship has been removed.
        assert!(!w.relationships.contains(&Relationship { subject: 0, object: 1, kind: RelationshipKind::Location("near".into()) }));
    }
}
