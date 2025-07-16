use std::collections::{HashMap, HashSet, VecDeque};
use std::hash::Hash;
use rand::{Rng, seq::IteratorRandom};
use std::fmt::Debug;

/// Types implementing this trait can be used as keys
/// for parameters when expanding a grammar.
/// 
/// This trait is automatically implemented on any type
/// satisfying the constraints.
pub trait ParameterKey: Hash + Eq + Clone + Debug {}
impl<T> ParameterKey for T where T: Hash + Eq + Clone + Debug {}

/// Types implementing this trait can be used as keys
/// for tags when expanding a grammar.
/// 
/// This trait is automatically implemented on any type
/// satisfying the constraints.
pub trait TagKey: Hash + Eq + Clone + Debug {}
impl<T> TagKey for T where T: Hash + Eq + Clone + Debug {}

/// Error returned when parsing a grammar from a string fails.
#[derive(PartialEq, Eq, Debug)]
pub enum RGrammarParseError {
    /// A parameter/symbol delimiter is not matched.
    UnmatchedDelimiter,
    /// A parameter/symbol is nested within another parameter/symbol.
    NestedDelimiter,
    /// A parameter/symbol token is empty.
    EmptyDelimiter,
    /// The given parameter string does not correspond to a valid key.
    UndefinedParameter
}

/// Error returned when expanding a grammar fails.
#[derive(PartialEq, Eq, Debug)]
pub enum RGrammarExpandError<K: ParameterKey> {
    /// The named rule is not known.
    UnknownRule(String),
    /// The given argument key does not correspond to a value.
    UndefinedArgument(K)
}

/// A replacement grammar.
/// 
/// A grammar is a collection of rules, each with a symbol,
/// and represents a "possibility space" of different string outputs.
/// 
/// Grammar rules can be parsed from strings or constructed
/// directly via the [rule!](crate::rule!) macro.
/// 
/// # Example
/// 
/// ```
/// use bardic::text::{RGrammar, RGrammarNode};
/// use bardic::rule;
/// use std::collections::HashMap;
/// use rand::SeedableRng;
/// use rand::rngs::StdRng;
/// 
/// // Create rules for the grammar.
/// let r1 = RGrammarNode::parse("[leader_role] [leader_name] of [leader_homeland]").unwrap();
/// let r2 = rule![RGrammarNode::symbol("leader_title".into()), RGrammarNode::text(" left in search of the ".into()), RGrammarNode::param("artifact".into())];
/// 
/// // Create grammar by assigning symbols to each rule.
/// let g = RGrammar::new(HashMap::from([
///     ("leader_title".into(), r1),
///     ("event_text".into(), r2)
/// ]));
/// 
/// // Expand the grammar into a concrete instance.
/// let mut rng = StdRng::from_os_rng();
/// let e = g.expand("event_text", &mut rng).unwrap();
/// 
/// // Define parameters for the grammar rendering.
/// let mut params = HashMap::new();
/// params.insert("leader_name".into(), "Arthur".to_string());
/// params.insert("leader_role".into(), "King".to_string());
/// params.insert("leader_homeland".into(), "Camelot".to_string());
/// params.insert("artifact".into(), "Holy Grail".to_string());
/// 
/// // Render the expansion into a string.
/// let s = g.render(&e, &params).unwrap();
/// // -> "King Arthur of Camelot left in search of the Holy Grail"
/// ```
#[derive(Debug)]
pub struct RGrammar<Param: ParameterKey, Tag: TagKey> {
    rules: HashMap<String, RGrammarNode<Param, Tag>>
}


impl<Param: ParameterKey, Tag: TagKey> RGrammar<Param, Tag> {
    /// Create a new replacement grammar from a mapping of symbols to rules.
    pub fn new(rules: HashMap<String, RGrammarNode<Param, Tag>>) -> RGrammar<Param, Tag> {
        RGrammar { rules }
    }

    /// Expand this grammar using an RNG (used to resolve choices).
    /// 
    /// If successful, an expansion instance is returned that can be used
    /// later to render output from the grammar.
    /// If not, an error is returned that describes the reason why the grammar
    /// could not be expanded.
    pub fn expand<R: Rng>(&self, symbol: &str, rng: &mut R) -> Result<RGrammarExpansion<Tag>, RGrammarExpandError<Param>> {
        let mut expansion = RGrammarExpansion::new(symbol.to_string());

        let rule = self.rules.get(symbol).ok_or(RGrammarExpandError::UnknownRule(symbol.into()))?;
        rule.expand(&mut expansion, &self.rules, rng)?;

        Ok(expansion)
    }

    /// Render the string represented by an expansion of this grammar.
    /// The hash provides values for each parameter.
    /// 
    /// Returns the rendered string if successful, or an error indicating why rendering
    /// failed if not.
    pub fn render(&self, expansion: &RGrammarExpansion<Tag>, params: &HashMap<Param, String>) -> Result<String, RGrammarExpandError<Param>> {
        self.render_with(expansion, &|p| params.get(p).cloned())
    }

    /// Render the string represented by the given expansion of this grammar.
    /// The function `f` provides values for each parameter. This function should return
    /// `Some` if a parameter key is valid, and `None` if not (which will result in an expansion error).
    /// 
    /// Returns the rendered string if successful, or an error indicating why rendering
    /// failed if not.
    pub fn render_with(&self, expansion: &RGrammarExpansion<Tag>, f: &dyn Fn(&Param) -> Option<String>) -> Result<String, RGrammarExpandError<Param>> {
        let mut choices = expansion.choices.clone();
        let rule = self.rules.get(&expansion.symbol).ok_or(RGrammarExpandError::UnknownRule(expansion.symbol.clone()))?;
        rule.render(&self.rules, &mut choices, f)
    }
}

/// A single node in a grammar.
#[derive(Clone, Debug)]
pub struct RGrammarNode<Param: ParameterKey, Tag: TagKey> {
    tags: HashSet<Tag>,
    constraints: HashSet<Tag>,
    inner: RGrammarNodeInner<Param, Tag>
}

impl<Param: ParameterKey, Tag: TagKey> RGrammarNode<Param, Tag> {
    /// Parse a string into a grammar rule, using a function to assign parameter keys.
    pub fn parse_with(s: &str, f: &dyn Fn(&str) -> Option<Param>) -> Result<Self, RGrammarParseError> {
        let mut parts = Vec::new();
        let mut current = String::new();
        let mut in_param = false;
        let mut in_symbol = false;

        for c in s.chars() {
            match c {
                '[' => {
                    if in_param || in_symbol {
                        return Err(RGrammarParseError::NestedDelimiter);
                    }

                    if !current.is_empty() {
                        parts.push(RGrammarNodeInner::Text(current.clone()));
                        current.clear();
                    }
                    in_param = true;
                }
                ']' => {
                    if !in_param {
                        return Err(RGrammarParseError::UnmatchedDelimiter)
                    }
                    else if current.is_empty() {
                        return Err(RGrammarParseError::EmptyDelimiter)
                    }

                    parts.push(RGrammarNodeInner::ParameterRef(f(&current).ok_or(RGrammarParseError::UndefinedParameter)?));
                    current.clear();
                    in_param = false;
                }
                '{' => {
                    if in_param || in_symbol {
                        return Err(RGrammarParseError::NestedDelimiter);
                    }

                    if !current.is_empty() {
                        parts.push(RGrammarNodeInner::Text(current.clone()));
                        current.clear();
                    }
                    in_symbol = true;
                }
                '}' => {
                    if !in_symbol {
                        return Err(RGrammarParseError::UnmatchedDelimiter);
                    }
                    else if current.is_empty() {
                        return Err(RGrammarParseError::EmptyDelimiter)
                    }

                    parts.push(RGrammarNodeInner::SymbolRef(current.clone()));
                    current.clear();
                    in_symbol = false;
                }
                _ => {
                    current.push(c);
                }
            }
        }

        // If we've reached here while still parsing a parameter,
        // we're missing a delimiter.
        if in_param {
            return Err(RGrammarParseError::UnmatchedDelimiter)
        }

        // Otherwise we may have a text element that needs adding.
        if !current.is_empty() {
            parts.push(RGrammarNodeInner::Text(current.into()))
        }

        let parts = parts.into_iter().map(|p| Self::from(p)).collect();

        let inner = RGrammarNodeInner::List(parts);
        let tags = HashSet::new();
        let constraints = HashSet::new();
        Ok(Self { tags, constraints, inner })
    }

    /// Create a list node with the given list of nodes.
    pub fn list(nodes: Vec<Self>) -> Self {
        let inner = RGrammarNodeInner::List(nodes);
        Self::new(inner)
    }

    /// Create a parameter node with the given key.
    pub fn param(key: Param) -> Self {
        let inner = RGrammarNodeInner::ParameterRef(key);
        Self::new(inner)
    }

    /// Create a symbol node with the given key.
    pub fn symbol(key: String) -> Self {
        let inner = RGrammarNodeInner::SymbolRef(key);
        Self::new(inner)
    }

    /// Create a text node with the given key.
    pub fn text(s: String) -> Self {
        let inner = RGrammarNodeInner::Text(s);
        Self::new(inner)
    }

    /// Create a choice node with the given set of nodes.
    pub fn choice(nodes: Vec<Self>) -> Self {
        let inner = RGrammarNodeInner::Choice(nodes);
        Self::new(inner)
    }

    /// Return this node with the given tag added.
    pub fn with_tag(mut self, t: &Tag) -> Self {
        self.tags.insert(t.clone());
        self
    }

    /// Return this node with the given tags added.
    pub fn with_tags(mut self, tags: &[Tag]) -> Self {
        for t in tags { self.tags.insert(t.clone()); }
        self
    }

    /// Return this node with the given constraint added.
    pub fn with_constraint(mut self, c: &Tag) -> Self {
        self.constraints.insert(c.clone());
        self
    }

    /// Return this node with the given constraints added.
    pub fn with_constraints(mut self, constraints: &[Tag]) -> Self {
        for c in constraints { self.constraints.insert(c.clone()); }
        self
    }

    fn new(inner: RGrammarNodeInner<Param, Tag>) -> Self {
        let tags = HashSet::new();
        let constraints = HashSet::new();
        Self {
            tags,
            constraints,
            inner
        }
    }

    /// Expands this node given a set of rules.
    /// Not intended to be used directly; instead the node is expanded by the RGrammar containing it.
    fn expand<R: Rng>(&self, exp: &mut RGrammarExpansion<Tag>, rules: &HashMap<String, Self>, rng: &mut R) -> Result<(), RGrammarExpandError<Param>> {
        // Add this node's tags to the expansion.
        exp.add_tags(&self.tags);

        match &self.inner {
            RGrammarNodeInner::Text(_) => Ok(()),
            RGrammarNodeInner::ParameterRef(_) => Ok(()),
            RGrammarNodeInner::SymbolRef(s) => rules.get(s).ok_or(RGrammarExpandError::UnknownRule(s.into()))?.expand(exp, rules, rng),
            RGrammarNodeInner::List(nodes) => {
                for n in nodes.iter() {
                    n.expand(exp, rules, rng)?
                }
                Ok(())
            },
            RGrammarNodeInner::Choice(nodes) => {
                // Pick a random index/node that matches the constraints.
                let nodes = nodes.iter().enumerate().filter(|(_, node)| exp.meets_constraints_for(node));
                let (pos, node) = nodes.choose(rng).unwrap();

                exp.choices.push_back(pos);

                node.expand(exp, rules, rng)
            }
        }
    }

    /// Renders a string for this rule.
    /// Not intended to be used directly; instead the node is rendered by the RGrammar containing it.
    fn render(&self, rules: &HashMap<String, Self>, choices: &mut VecDeque<usize>, f: &dyn Fn(&Param) -> Option<String>) -> Result<String, RGrammarExpandError<Param>> {
        match &self.inner {
            RGrammarNodeInner::Text(s) => Ok(s.into()),
            RGrammarNodeInner::ParameterRef(p) => f(&p).ok_or(RGrammarExpandError::UndefinedArgument(p.clone())),
            RGrammarNodeInner::SymbolRef(s) => {
                let rule = rules.get(s).ok_or(RGrammarExpandError::UnknownRule(s.clone()))?;
                rule.render(rules, choices, f)
            }
            RGrammarNodeInner::List(nodes) => {
                let mut s = String::new();
                for node in nodes {
                    s.push_str(&node.render(rules, choices, f)?);
                }
                Ok(s)
            },
            RGrammarNodeInner::Choice(nodes) => {
                // Get the choice from the expansion.
                let choice = choices.pop_front().unwrap();

                // Render the selected sub-node.
                nodes.get(choice).unwrap().render(rules, choices, f)
            }
        }
    }
}

impl RGrammarNode<String, String> {
    /// Parse a string into a rule where parameter/tag keys are strings.
    pub fn parse(s: &str) -> Result<RGrammarNode<String, String>, RGrammarParseError> {
        let f = |p: &str| { Some(p.to_string()) };
        RGrammarNode::parse_with(s, &f)
    }
}

impl<Param: ParameterKey, Tag: TagKey> From<RGrammarNodeInner<Param, Tag>> for RGrammarNode<Param, Tag> {
    fn from(value: RGrammarNodeInner<Param, Tag>) -> Self {
        let tags = HashSet::new();
        let constraints = HashSet::new();
        let inner = value;
        Self { tags, constraints, inner }
    }
}

/// An inner type representing different kinds of grammar nodes.
/// Should not be used directly. Use [RGrammarNode] instead.
#[derive(Clone, Debug)]
enum RGrammarNodeInner<Param: ParameterKey, Tag: TagKey> {
    Text(String),
    ParameterRef(Param),
    SymbolRef(String),
    List(Vec<RGrammarNode<Param, Tag>>),
    Choice(Vec<RGrammarNode<Param, Tag>>)
}

/// The result of expanding a grammar.
/// 
/// An instance of this struct can be stored to deterministically
/// render an output of the expanded grammar in future.
pub struct RGrammarExpansion<T: TagKey> {
    tags: HashSet<T>,
    choices: VecDeque<usize>,
    symbol: String
}

impl<T: TagKey> RGrammarExpansion<T> {
    /// Returns the tags created during expansion of the grammar.
    pub fn tags(&self) -> &HashSet<T> {
        &self.tags
    }

    fn new(symbol: String) -> Self {
        let tags = HashSet::new();
        let choices = VecDeque::new();
        Self { tags, choices, symbol }
    }

    fn add_tags(&mut self, tags: &HashSet<T>) {
        for t in tags { self.tags.insert(t.clone()); }
    }

    /// Does this expansion meet all constraints for the given node?
    fn meets_constraints_for<P: ParameterKey>(&self, node: &RGrammarNode<P, T>) -> bool {
        node.constraints.is_subset(&self.tags)
    }
}

/// Provides a shorthand for creating an [RGrammarNode]
/// from a list of sub-nodes.
#[macro_export]
macro_rules! rule {
    ($($a:expr),*) => {
        RGrammarNode::list(vec![$($a),*])
    };
}

#[cfg(test)]
mod tests {
    use rand::rngs::StdRng;
    use rand::SeedableRng;

    use super::*;

    fn simple_grammar<P: ParameterKey>(r: RGrammarNode<P, String>) -> RGrammar<P, String> {
        RGrammar::new(HashMap::from([("s".into(), r)]))
    }

    fn expand_and_render_params<P: ParameterKey, T: TagKey>(g: &RGrammar<P, T>, s: &str, r: &mut StdRng, p: &HashMap<P, String>) -> String
    {
        let e = g.expand(s, r).unwrap();
        g.render(&e, p).unwrap()
    }

    /// Tests simple grammar expansion.
    #[test]
    fn test_simple_grammar() {
        let g = simple_grammar(rule![RGrammarNode::param("name"), RGrammarNode::text(" is here!".into())]);

        let mut params = HashMap::new();
        params.insert("name", "Bob".to_string());

        assert_eq!("Bob is here!", &expand_and_render_params(&g, "s", &mut StdRng::from_os_rng(), &params));
    }

    /// Tests that a sensible error is returned when rendering fails.
    #[test]
    fn test_render_error() {
        let g = simple_grammar(rule![RGrammarNode::param("foo")]);
        let e = g.expand("s", &mut StdRng::from_os_rng()).unwrap();
        
        let e = g.render(&e, &HashMap::new());
        assert_eq!(Err(RGrammarExpandError::UndefinedArgument("foo")), e);
    }

    /// Tests that grammars can be expanded recursively.
    #[test]
    fn test_recursive() {
        let rule_title = rule![RGrammarNode::param("name"), RGrammarNode::text(" of ".into()), RGrammarNode::param("place")];
        let rule_greeting = rule![RGrammarNode::text("Hello ".into()), RGrammarNode::symbol("title".into()), RGrammarNode::text("!".into())];

        let rules = HashMap::from([
            ("title".into(), rule_title),
            ("greeting".into(), rule_greeting)
        ]);

        let g = RGrammar::<&str, String>::new(rules);

        let mut params = HashMap::new();
        params.insert("name", "Bob".to_string());
        params.insert("place", "Halifax".to_string());

        assert_eq!("Hello Bob of Halifax!", &expand_and_render_params(&g, "greeting", &mut StdRng::from_os_rng(), &params))
    }

    /// Tests that a grammar rule can be parsed from a string.
    #[test]
    fn test_simple_parse() {
        let g = simple_grammar(RGrammarNode::parse("[name] is [action] at the moment").unwrap());

        let mut params = HashMap::new();
        params.insert("name".to_string(), "Steve".to_string());
        params.insert("action".to_string(), "gardening".to_string());

        assert_eq!("Steve is gardening at the moment", &expand_and_render_params(&g, "s", &mut StdRng::from_os_rng(), &params));
    }

    /// Tests various parsing error cases.
    #[test]
    fn test_parse_errors() {
        assert_eq!(RGrammarParseError::UnmatchedDelimiter, RGrammarNode::parse("Hello [name").unwrap_err());
        assert_eq!(RGrammarParseError::UnmatchedDelimiter, RGrammarNode::parse("name] is here!").unwrap_err());
        assert_eq!(RGrammarParseError::EmptyDelimiter, RGrammarNode::parse("[] is here!").unwrap_err());
        assert_eq!(RGrammarParseError::NestedDelimiter, RGrammarNode::parse("[[name]] is here!").unwrap_err());
        assert_eq!(RGrammarParseError::NestedDelimiter, RGrammarNode::parse("[{name}] is here!").unwrap_err());
    }

    /// Test that a grammar can be parsed with a function to determine parameter keys.
    #[test]
    fn test_parse_with_function() {
        let f = |p: &str| {
            let p = match p {
                "a" => 0,
                "b" => 1,
                _ => 2
            };
            Some(p)
        };

        let g = simple_grammar(RGrammarNode::parse_with("[a] is next to [b], which is next to [d]", &f).unwrap());

        let mut params = HashMap::new();
        params.insert(0, "foo".into());
        params.insert(1, "bar".into());
        params.insert(2, "baz".into());

        assert_eq!("foo is next to bar, which is next to baz", &expand_and_render_params(&g, "s", &mut StdRng::from_os_rng(), &params));
    }

    /// Test that a grammar can be expanded with a function to determine parameter values.
    #[test]
    fn test_expand_with_function() {
        let g = simple_grammar(RGrammarNode::parse("Hello [name]!").unwrap());

        let f = |p: &String| {
            if p == "name" {
                Some("Steve".into())
            }
            else {
                None
            }
        };

        let e = g.expand("s", &mut StdRng::from_os_rng()).unwrap();

        assert_eq!("Hello Steve!", g.render_with(&e, &f).unwrap());
    }

    /// Test that grammar rules can be parsed with references to other rules.
    #[test]
    fn test_parse_with_function_subgrammar() {
        let r1 = RGrammarNode::parse("hello to [b]").unwrap();
        let r2 = RGrammarNode::parse("[a] says {greeting}").unwrap();

        let rules = HashMap::from([
            ("greeting".into(), r1),
            ("s".into(), r2)
        ]);
        let g = RGrammar::new(rules);

        let mut params = HashMap::new();
        params.insert("a".into(), "Steve".into());
        params.insert("b".into(), "Bob".into());

        assert_eq!("Steve says hello to Bob", &expand_and_render_params(&g, "s", &mut StdRng::from_os_rng(), &params));
    }

    /// Test that grammar rules can include choices.
    /// For the purposes of this test only a single choice is provided.
    #[test]
    fn test_choice() {
        let g = simple_grammar::<String>(rule!(RGrammarNode::choice(vec![RGrammarNode::text("hello".into())])));

        assert_eq!("hello", &expand_and_render_params(&g, "s", &mut StdRng::from_os_rng(), &HashMap::new()));
    }

    /// Test that tags in nodes are considered during future expansion.
    #[test]
    fn test_choice_constraint() {
        let n1 = RGrammarNode::text("first ".into()).with_tag(&1);
        let n2 = RGrammarNode::choice(vec![RGrammarNode::text("second ".into()).with_constraint(&2), RGrammarNode::text("first ".into()).with_constraint(&1).with_tag(&2)]);
        let n3 = RGrammarNode::choice(vec![RGrammarNode::text("first, second".into()).with_constraints(&[1, 2]), RGrammarNode::text("third".into()).with_constraint(&3)]);

        let g = HashMap::from([("s".into(), rule![n1, n2, n3])]);
        let g = RGrammar::<&str, _>::new(g);

        let mut rng = StdRng::from_os_rng();

        // Run the expansion many times to be sure of a failure
        // if the constraints are not being considered.
        for _ in 0..1000 {
            let s = &expand_and_render_params(&g, "s", &mut rng, &HashMap::new());
            assert_eq!("first first first, second", s);
        }
    }

    /// Test that rendering is deterministic.
    #[test]
    fn test_render_determinism() {
        let g = simple_grammar(rule![RGrammarNode::<&str, String>::choice(vec![RGrammarNode::text("foo".into()), RGrammarNode::text("bar".into())])]);
        let e = RGrammarExpansion {
            tags: HashSet::new(),
            choices: VecDeque::from([1]),
            symbol: "s".into()
        };

        for _ in 0..1000 {
            let s = &g.render(&e, &HashMap::new()).unwrap();
            assert_eq!("bar", s);
        }
    }
}
