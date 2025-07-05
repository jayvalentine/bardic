# Bardic

Bardic is a Rust toolbox for building procedural narratives at scale.

## Features

### Text Generation

Bardic provides facilities for procedural text generation through
replacement grammars, allowing the construction of prose by composing
properties of entities in your system.

For example the grammar:

```
event_text => [leader_title] left in search of the [artifact]

leader_title => [leader_role] [leader_name] of [leader_homeland]
```

given the following parameters:

```
leader_name => Arthur
leader_role => King
leader_homeland => Camelot
artifact => Holy Grail
```

results in the following expanded text:

```
King Arthur of Camelot left in search of the Holy Grail
```

When procedurally-generated properties are used to expand the fields
of the grammar, varied text can be generated for entities in your system.

The grammar above can be described using Bardic's `RGrammar` struct.
