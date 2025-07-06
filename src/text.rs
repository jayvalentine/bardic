use std::collections::HashMap;
use std::hash::Hash;

pub trait ParameterKey: Hash + Eq + Clone {}
impl<T> ParameterKey for T where T: Hash + Eq + Clone {}

/// Represents a replacement grammar that can be expanded
/// based on some set of properties.
/// 
/// A grammar is a collection of rules, each with a symbol.
/// 
/// Grammars can be constructed from strings or directly
/// using sub-grammar objects (via the rgrammar! macro).
/// 
/// # Examples
/// 
/// ```
/// use bardic::text::{RGrammar, RGrammarNode};
/// use bardic::rule;
/// use std::collections::HashMap;
/// 
/// let r1 = RGrammarNode::parse("[leader_role] [leader_name] of [leader_homeland]").unwrap();
/// let r2 = rule![RGrammarNode::SymbolRef("leader_title".into()), RGrammarNode::Text(" left in search of the ".into()), RGrammarNode::ParameterRef("artifact".into())];
/// 
/// let g = RGrammar::new(HashMap::from([
///     ("leader_title".into(), r1),
///     ("event_text".into(), r2)
/// ]));
/// 
/// let mut params = HashMap::new();
/// params.insert("leader_name".into(), "Arthur".to_string());
/// params.insert("leader_role".into(), "King".to_string());
/// params.insert("leader_homeland".into(), "Camelot".to_string());
/// params.insert("artifact".into(), "Holy Grail".to_string());
/// 
/// let s = g.expand("event_text", &params).unwrap();
/// // -> "King Arthur of Camelot left in search of the Holy Grail"
/// ```
#[derive(Debug)]
pub struct RGrammar<K: ParameterKey> {
    rules: HashMap<String, RGrammarNode<K>>
}

#[derive(Debug)]
pub enum RGrammarNode<K: ParameterKey> {
    Text(String),
    ParameterRef(K),
    SymbolRef(String),
    List(Vec<RGrammarNode<K>>)
}

#[derive(PartialEq, Eq, Debug)]
pub enum RGrammarExpandError<K: ParameterKey> {
    /// The named rule is not known.
    UnknownRule(String),
    /// The given argument key does not correspond to a value.
    UndefinedArgument(K)
}

impl<K: ParameterKey> RGrammarNode<K> {
    /// Expands this node given a set of rules and function providing parameter values.
    fn expand_with(&self, rules: &HashMap<String, RGrammarNode<K>>, f: &dyn Fn(&K) -> Option<String>) -> Result<String, RGrammarExpandError<K>> {
        match self {
            RGrammarNode::Text(s) => Ok(s.to_string()),
            RGrammarNode::ParameterRef(k) => f(k).ok_or(RGrammarExpandError::UndefinedArgument(k.clone())),
            RGrammarNode::SymbolRef(s) => rules.get(s).ok_or(RGrammarExpandError::UnknownRule(s.into()))?.expand_with(rules, f),
            RGrammarNode::List(nodes) => {
                let mut strings = Vec::new();
                for n in nodes.iter() {
                    let e = n.expand_with(rules, f)?;
                    strings.push(e);
                }
                Ok(strings.join(""))
            }
        }
    }

    /// Parse a string into a grammar rule, using a function to assign
    /// parameter keys.
    pub fn parse_with(s: &str, f: &dyn Fn(&str) -> Option<K>) -> Result<RGrammarNode<K>, RGrammarParseError> {
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
                        parts.push(RGrammarNode::Text(current.clone()));
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

                    parts.push(RGrammarNode::ParameterRef(f(&current).ok_or(RGrammarParseError::UndefinedParameter)?));
                    current.clear();
                    in_param = false;
                }
                '{' => {
                    if in_param || in_symbol {
                        return Err(RGrammarParseError::NestedDelimiter);
                    }

                    if !current.is_empty() {
                        parts.push(RGrammarNode::Text(current.clone()));
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

                    parts.push(RGrammarNode::SymbolRef(current.clone()));
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
            parts.push(RGrammarNode::Text(current.into()))
        }

        Ok(RGrammarNode::List(parts))
    }
}

impl RGrammarNode<String> {
    pub fn parse(s: &str) -> Result<RGrammarNode<String>, RGrammarParseError> {
        let f = |p: &str| { Some(p.to_string()) };
        RGrammarNode::<String>::parse_with(s, &f)
    }
}

impl<K: ParameterKey> RGrammar<K> {
    /// Create a new replacement grammar from a set of rules.
    pub fn new(rules: HashMap<String, RGrammarNode<K>>) -> RGrammar<K> {
        RGrammar { rules }
    }

    /// Expand this grammar given a function to map parameter keys to values.
    /// 
    /// The function should return Some(value) when given a valid key,
    /// and None when given an invalid key.
    pub fn expand_with(&self, symbol: &str, f: &dyn Fn(&K) -> Option<String>) -> Result<String, RGrammarExpandError<K>> {
        let rule = self.rules.get(symbol).ok_or(RGrammarExpandError::UnknownRule(symbol.into()))?;
        Ok(rule.expand_with(&self.rules, f)?)
    }

    /// Expand this grammar given a map of parameter keys => values.
    pub fn expand(&self, symbol: &str, params: &HashMap<K, String>) -> Result<String, RGrammarExpandError<K>> {
        self.expand_with(symbol, &|p| { params.get(p).cloned() })
    }
}

/// Provides a shorthand for creating an RGrammar
/// from a list of components.
#[macro_export]
macro_rules! rule {
    ($($a:expr),*) => {
        RGrammarNode::List(vec![$($a),*])
    };
}

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

#[cfg(test)]
mod tests {
    use super::*;

    fn simple_grammar<K: ParameterKey>(r: RGrammarNode<K>) -> RGrammar<K> {
        RGrammar::new(HashMap::from([("s".into(), r)]))
    }

    /// Tests simple grammar expansion.
    #[test]
    fn test_simple_grammar() {
        let g = simple_grammar(rule![RGrammarNode::ParameterRef("name"), RGrammarNode::Text(" is here!".into())]);

        let mut params = HashMap::new();
        params.insert("name", "Bob".to_string());

        assert_eq!("Bob is here!", &g.expand("s", &params).unwrap());
    }

    /// Tests that a sensible error is returned when expansion fails.
    #[test]
    fn test_expansion_error() {
        let g = simple_grammar(rule![RGrammarNode::ParameterRef("foo")]);
        let params = HashMap::new();
        
        let e = g.expand("s", &params);
        assert_eq!(Err(RGrammarExpandError::UndefinedArgument("foo")), e);
    }

    /// Tests that grammars can be expanded recursively.
    #[test]
    fn test_recursive() {
        let rule_title = rule![RGrammarNode::ParameterRef("name"), RGrammarNode::Text(" of ".into()), RGrammarNode::ParameterRef("place")];
        let rule_greeting = rule![RGrammarNode::Text("Hello ".into()), RGrammarNode::SymbolRef("title".into()), RGrammarNode::Text("!".into())];

        let rules = HashMap::from([
            ("title".into(), rule_title),
            ("greeting".into(), rule_greeting)
        ]);

        let g = RGrammar::new(rules);

        let mut params = HashMap::new();
        params.insert("name", "Bob".to_string());
        params.insert("place", "Halifax".to_string());

        assert_eq!("Hello Bob of Halifax!", &g.expand("greeting", &params).unwrap())
    }

    /// Tests that a grammar rule can be parsed from a string.
    #[test]
    fn test_simple_parse() {
        let g = simple_grammar(RGrammarNode::parse("[name] is [action] at the moment").unwrap());

        let mut params = HashMap::new();
        params.insert("name".to_string(), "Steve".to_string());
        params.insert("action".to_string(), "gardening".to_string());

        assert_eq!("Steve is gardening at the moment", &g.expand("s", &params).unwrap());
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

        assert_eq!("foo is next to bar, which is next to baz", g.expand("s", &params).unwrap());
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

        assert_eq!("Hello Steve!", g.expand_with("s", &f).unwrap());
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

        assert_eq!("Steve says hello to Bob", g.expand("s", &params).unwrap());
    }
}
