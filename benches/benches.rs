use criterion::*;
use rand::rngs::StdRng;
use rand::seq::IteratorRandom;
use rand::SeedableRng;
use rand::prelude::IndexedRandom;
use std::collections::{HashMap, HashSet};

use bardic::text::*;
use bardic::entity::*;

fn expand_grammar(g: &RGrammar<String, String>, rng: &mut StdRng, symbol: &str) {
    g.expand(symbol, rng, HashSet::new());
}

fn benchmark_grammar_expansion(c: &mut Criterion) {
    let r1 = ('a'..='z').map(|c| format!("{{{c}}}")).collect::<Vec<String>>().join(" ! ");
    let r1 = RGrammarNode::parse(&r1).unwrap();

    let r2 = ('0'..='9').map(|c| format!("[{c}]")).collect::<Vec<String>>().join("");
    let r2 = RGrammarNode::parse(&r2).unwrap();

    let mut g = HashMap::new();
    for s in 'a'..='z' {
        g.insert(s.to_string(), r2.clone());
    }
    g.insert("text".into(), r1);
    let g = RGrammar::new(g).unwrap();

    let mut rng = StdRng::from_os_rng();

    c.bench_function("grammar_expand", |b| b.iter(|| expand_grammar(&g, &mut rng, "text")));
}

struct BenchmarkEntity {
    id: u32
}

impl Entity<u32, u32> for BenchmarkEntity {
    fn id(&self) -> &u32 {
        &self.id
    }

    fn has_tag(&self, t: &u32) -> bool {
        false
    }

    fn possible_actions(&self, s: &WorldState<u32>) -> Vec<(u32, Action<u32>)> {
        let mut actions = Vec::new();

        for r in s.with_subject(self) {
            match r.kind() {
                RelationshipKind::Location(s) => {
                    if s == "near" {
                        actions.push(Action::new(
                            HashSet::from([
                                Relationship::new(self.id, *r.object(), RelationshipKind::Location("near".into())),
                                Relationship::new(*r.object(), self.id, RelationshipKind::Location("near".into())),
                            ]),
                            HashSet::from([
                                Relationship::new(self.id, *r.object(), RelationshipKind::Location("far".into())),
                                Relationship::new(*r.object(), self.id, RelationshipKind::Location("far".into())),
                            ]),
                        ))
                    } else if s == "far" {
                        actions.push(Action::new(
                            HashSet::from([
                                Relationship::new(self.id, *r.object(), RelationshipKind::Location("far".into())),
                                Relationship::new(*r.object(), self.id, RelationshipKind::Location("far".into())),
                            ]),
                            HashSet::from([
                                Relationship::new(self.id, *r.object(), RelationshipKind::Location("near".into())),
                                Relationship::new(*r.object(), self.id, RelationshipKind::Location("near".into())),
                            ]),
                        ))
                    }
                }
            }
        }

        actions.into_iter().map(|a| (1, a)).collect()
    }
}

fn world_iteration(w: &mut WorldState<u32>, rng: &mut StdRng, entities: &Vec<BenchmarkEntity>) {
    // Apply a random action for each entity.
    for e in entities {
        let actions = e.possible_actions(w);
        match actions.choose(rng) {
            Some(a) => w.apply_action(&a.1),
            None => ()
        }
    }
}

fn benchmark_world_state(c: &mut Criterion) {
    let mut rng = StdRng::from_os_rng();

    // Create a large number of entities.
    let mut entities = Vec::new();
    for id in 0..1000 {
        entities.push(BenchmarkEntity { id })
    }

    // Create a relationship for each entity.
    let mut world = WorldState::new();
    let locations = ["near", "far"];
    let mut others: HashSet<u32> = entities.iter().map(|e2| e2.id().clone()).collect();

    for e in &entities {
        others.remove(e.id());

        let object = others.iter().choose(&mut rng);

        if object.is_some() {
            let r = Relationship::new(*e.id(), *object.unwrap(), RelationshipKind::Location(locations.choose(&mut rng).unwrap().to_string()));
            world.add_relationship(r);
        }
    }

    c.bench_function("world_iteration", |b| b.iter(|| world_iteration(&mut world, &mut rng, &entities)));
}

criterion_group!(benches, benchmark_grammar_expansion, benchmark_world_state);
criterion_main!(benches);
