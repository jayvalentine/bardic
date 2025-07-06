use criterion::*;
use bardic::text::*;
use std::collections::HashMap;

fn expand_grammar(g: &RGrammar<String>, symbol: &str, params: &HashMap<String, String>) {
    g.expand(symbol, params).unwrap();
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
    let g = RGrammar::new(g);

    let mut p = HashMap::new();
    for i in '0'..='9' {
        p.insert(i.into(), format!("number {i}"));
    }

    c.bench_function("grammar_expand", |b| b.iter(|| expand_grammar(&g, "text", &p)));
}

criterion_group!(benches, benchmark_grammar_expansion);
criterion_main!(benches);
