use std::collections::HashMap;
use std::hash::Hash;

pub trait ParameterKey: Hash + Eq + Clone {}
impl<T> ParameterKey for T where T: Hash + Eq + Clone {}

/// Represents a replacement grammar that can be expanded
/// based on some set of properties.
/// 
/// Grammars can be constructed from strings or directly
/// using sub-grammar objects (via the rgrammar! macro).
/// 
/// # Examples
/// 
/// ```
/// use bardic::text::{RGrammar, RGrammarPart};
/// use bardic::rgrammar;
/// use std::collections::HashMap;
/// 
/// let leader_title = RGrammar::parse("[leader_role] [leader_name] of [leader_homeland]").unwrap();
/// let event_text = rgrammar![RGrammarPart::subgrammar(leader_title), RGrammarPart::text(" left in search of the "), RGrammarPart::param("artifact".into())];
/// 
/// let mut params = HashMap::new();
/// params.insert("leader_name".into(), "Arthur".to_string());
/// params.insert("leader_role".into(), "King".to_string());
/// params.insert("leader_homeland".into(), "Camelot".to_string());
/// params.insert("artifact".into(), "Holy Grail".to_string());
/// 
/// let s = event_text.expand(&params).unwrap();
/// // -> "King Arthur of Camelot left in search of the Holy Grail"
/// ```
#[derive(Debug)]
pub struct RGrammar<K: ParameterKey> {
    parts: Vec<RGrammarPart<K>>
}

#[derive(PartialEq, Eq, Debug)]
pub enum RGrammarExpandError<K: Hash + Clone> {
    UndefinedArgument(K)
}

impl<K: ParameterKey> RGrammar<K> {
    /// Create a new replacement grammar from a vector of components.
    pub fn new(parts: Vec<RGrammarPart<K>>) -> RGrammar<K> {
        RGrammar { parts }
    }

    /// Expand this grammar given a function to map parameter keys to values.
    /// 
    /// The function should return Some(value) when given a valid key,
    /// and None when given an invalid key.
    pub fn expand_with(&self, f: &dyn Fn(&K) -> Option<String>) -> Result<String, RGrammarExpandError<K>> {
        let mut strings = Vec::new();
        for p in &self.parts {
            strings.push(p.expand_with(f)?);
        }

        Ok(strings.join(""))
    }

    /// Expand this grammar given a map of parameter keys => values.
    pub fn expand(&self, params: &HashMap<K, String>) -> Result<String, RGrammarExpandError<K>> {
        self.expand_with(&|p| { params.get(p).cloned() })
    }

    /// Parse a string into a grammar using a function to determine sub-components
    /// from strings in the input.
    pub fn parse_with(s: &str, f: &dyn Fn(&str) -> Option<RGrammarPart<K>>) -> Result<RGrammar<K>, RGrammarParseError> {
        let mut parts = Vec::new();
        let mut current = String::new();
        let mut in_param = false;

        for c in s.chars() {
            match c {
                '[' => {
                    if in_param {
                        return Err(RGrammarParseError::NestedParameterDelimiter);
                    }

                    if !current.is_empty() {
                        parts.push(RGrammarPart::text(&current));
                        current.clear();
                    }
                    in_param = true;
                }
                ']' => {
                    if !in_param {
                        return Err(RGrammarParseError::UnmatchedParameterDelimiter)
                    }
                    else if current.is_empty() {
                        return Err(RGrammarParseError::EmptyParameter)
                    }

                    parts.push(f(&current).ok_or(RGrammarParseError::UndefinedParameter)?);
                    current.clear();
                    in_param = false;
                }
                _ => {
                    current.push(c);
                }
            }
        }

        // If we've reached here while still parsing a parameter,
        // we're missing a delimiter.
        if in_param {
            return Err(RGrammarParseError::UnmatchedParameterDelimiter)
        }

        // Otherwise we may have a text element that needs adding.
        if !current.is_empty() {
            parts.push(RGrammarPart::text(&current))
        }

        Ok(RGrammar::new(parts))
    }
}

/// Provides a shorthand for creating an RGrammar
/// from a list of components.
#[macro_export]
macro_rules! rgrammar {
    ($($a:expr),*) => {
        RGrammar::new(vec![$($a),*])
    };
}

/// Error returned when parsing a grammar from a string fails.
#[derive(PartialEq, Eq, Debug)]
pub enum RGrammarParseError {
    UnmatchedParameterDelimiter,
    NestedParameterDelimiter,
    EmptyParameter,
    UndefinedParameter
}

impl RGrammar<String> {
    /// Parses a simple grammar where strings are used
    /// as parameter keys (and therefore no mapping is required).
    pub fn parse(s: &str) -> Result<Self, RGrammarParseError> {
        RGrammar::<String>::parse_with(s, &|p| { Some(RGrammarPart::param(String::from(p))) })
    }
}

/// A part of a replacement grammar.
#[derive(Debug)]
pub enum RGrammarPart<K: ParameterKey> {
    Text(String),
    Parameter(K),
    SubGrammar(RGrammar<K>),
}

impl<K: ParameterKey> RGrammarPart<K> {
    /// Create a grammar part representing literal text.
    pub fn text(s: &str) -> RGrammarPart<K> {
        RGrammarPart::<K>::Text(s.to_string())
    }

    /// Create a grammar part representing a parameter.
    pub fn param(k: K) -> RGrammarPart<K> {
        RGrammarPart::<K>::Parameter(k)
    }

    /// Create a grammar part referencing another grammar.
    pub fn subgrammar(g: RGrammar<K>) -> RGrammarPart<K> {
        RGrammarPart::<K>::SubGrammar(g)
    }

    pub fn expand_with(&self, f: &dyn Fn(&K) -> Option<String>) -> Result<String, RGrammarExpandError<K>> {
        match self {
            Self::Text(t) => Ok(t.clone()),
            Self::Parameter(k) => match f(k) {
                Some(v) => Ok(v.clone()),
                None => Err(RGrammarExpandError::UndefinedArgument(k.clone()))
            },
            Self::SubGrammar(g) => g.expand_with(f)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Tests simple grammar expansion.
    #[test]
    fn test_simple_grammar() {
        let g = rgrammar![RGrammarPart::param("name"), RGrammarPart::text(" is here!")];

        let mut params = HashMap::new();
        params.insert("name", "Bob".to_string());

        assert_eq!("Bob is here!", &g.expand(&params).unwrap());
    }

    /// Tests that a sensible error is returned when expansion fails.
    #[test]
    fn test_expansion_error() {
        let g = rgrammar![RGrammarPart::param("foo")];
        let params = HashMap::new();
        
        let e = g.expand(&params);
        assert_eq!(Err(RGrammarExpandError::UndefinedArgument("foo")), e);
    }

    /// Tests that grammars can be expanded recursively.
    #[test]
    fn test_recursive() {
        let sg = rgrammar![RGrammarPart::param("name"), RGrammarPart::text(" of "), RGrammarPart::param("place")];
        let g = rgrammar![RGrammarPart::text("Hello "), RGrammarPart::subgrammar(sg), RGrammarPart::text("!")];

        let mut params = HashMap::new();
        params.insert("name", "Bob".to_string());
        params.insert("place", "Halifax".to_string());

        assert_eq!("Hello Bob of Halifax!", &g.expand(&params).unwrap())
    }

    /// Tests that a grammar can be parsed from a string.
    #[test]
    fn test_simple_parse() {
        let g = RGrammar::parse("[name] is [action] at the moment").unwrap();

        let mut params = HashMap::new();
        params.insert("name".to_string(), "Steve".to_string());
        params.insert("action".to_string(), "gardening".to_string());

        assert_eq!("Steve is gardening at the moment", &g.expand(&params).unwrap());
    }

    /// Tests various parsing error cases.
    #[test]
    fn test_parse_errors() {
        assert_eq!(RGrammarParseError::UnmatchedParameterDelimiter, RGrammar::parse("Hello [name").unwrap_err());
        assert_eq!(RGrammarParseError::UnmatchedParameterDelimiter, RGrammar::parse("name] is here!").unwrap_err());
        assert_eq!(RGrammarParseError::EmptyParameter, RGrammar::parse("[] is here!").unwrap_err());
        assert_eq!(RGrammarParseError::NestedParameterDelimiter, RGrammar::parse("[[name]] is here!").unwrap_err());
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
            Some(RGrammarPart::param(p))
        };

        let g = RGrammar::parse_with("[a] is next to [b], which is next to [d]", &f).unwrap();

        let mut params = HashMap::new();
        params.insert(0, "foo".into());
        params.insert(1, "bar".into());
        params.insert(2, "baz".into());

        assert_eq!("foo is next to bar, which is next to baz", g.expand(&params).unwrap());
    }

    /// Test that a grammar can be expanded with a function to determine parameter values.
    #[test]
    fn test_expand_with_function() {
        let g = RGrammar::parse("Hello [name]!").unwrap();

        let f = |p: &String| {
            if p == "name" {
                Some("Steve".into())
            }
            else {
                None
            }
        };

        assert_eq!("Hello Steve!", g.expand_with(&f).unwrap());
    }

    /// Test that a grammar can be parsed with a function that inserts other grammars.
    #[test]
    fn test_parse_with_function_subgrammar() {
        let f = |p: &str| {
            match p {
                "a" => Some(RGrammarPart::param("a")),
                "greeting" => Some(RGrammarPart::subgrammar(rgrammar![RGrammarPart::text("hello to "), RGrammarPart::Parameter("b")])),
                _ => None
            }
        };

        let g = RGrammar::parse_with("[a] says [greeting]", &f).unwrap();

        let mut params = HashMap::new();
        params.insert("a", "Steve".into());
        params.insert("b", "Bob".into());

        assert_eq!("Steve says hello to Bob", g.expand(&params).unwrap());
    }
}
