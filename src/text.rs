use std::str::FromStr;
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
/// use bardic::text::RGrammar;
/// 
/// let leader_title = RGrammar::from_string("[leader_role] [leader_name] of [leader_homeland]").unwrap();
/// let event_text = rgrammar![RGrammarPart::subgrammar(leader_title), RGrammarPart::text(" left in search of the "), RGrammarPart::param("artifact")];
/// 
/// let mut params = HashMap::new();
/// params.insert("leader_name", "Arthur".to_string());
/// params.insert("leader_role", "King".to_string());
/// params.insert("leader_homeland", "Camelot".to_string());
/// params.insert("artifact", "Holy Grail".to_string());
/// 
/// let s = event_text.expand(&params).unwrap();
/// // -> "King Arthur of Camelot left in search of the Holy Grail"
/// ```
pub struct RGrammar<K: ParameterKey> {
    parts: Vec<RGrammarPart<K>>
}

#[derive(PartialEq, Eq, Debug)]
pub enum RGrammarExpandError<K: Hash + Clone> {
    UndefinedArgument(K)
}

impl<K: ParameterKey> RGrammar<K> {
    pub fn new(parts: Vec<RGrammarPart<K>>) -> RGrammar<K> {
        RGrammar { parts }
    }

    /// Expand this grammar given a map of parameter keys => values.
    pub fn expand(&self, params: &HashMap<K, String>) -> Result<String, RGrammarExpandError<K>> {
        let mut strings = Vec::new();
        for p in &self.parts {
            strings.push(p.expand(params)?);
        }

        Ok(strings.join(""))
    }
}

/// Provides a shorthand for creating an RGrammar
/// from a list of components.
macro_rules! rgrammar {
    ($($a:expr),*) => {
        RGrammar::new(vec![$($a),*])
    };
}

#[derive(PartialEq, Eq, Debug)]
pub enum RGrammarParseError {
    UnterminatedParameter(String)
}

impl RGrammar<&str> {
    /// Parses a simple grammar where strings are used
    /// as parameter keys (and therefore no mapping is required).
    fn parse(s: &str) -> Result<Self, RGrammarParseError> {
        Ok(RGrammar::<&str> {
            parts: vec![]
        })
    }
}

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

    pub fn expand(&self, params: &HashMap<K, String>) -> Result<String, RGrammarExpandError<K>> {
        match self {
            Self::Text(t) => Ok(t.clone()),
            Self::Parameter(k) => match params.get(k) {
                Some(v) => Ok(v.clone()),
                None => Err(RGrammarExpandError::UndefinedArgument(k.clone()))
            },
            Self::SubGrammar(g) => g.expand(params)
        }
    }
}

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
        let g = RGrammar::parse("[name] is currently [action]").unwrap();

        let mut params = HashMap::new();
        params.insert("name", "Steve".to_string());
        params.insert("action", "gardening".to_string());

        assert_eq!("Steve is currently gardening", &g.expand(&params).unwrap());
    }
}
