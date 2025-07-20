#![deny(missing_docs)]

//! Bardic provides performant building blocks for creating large-scale
//! procedural narrative generators.

/// Provides types for managing unique IDs within a system.
/// 
/// IDs can be used to represent properties/states of entities
/// without needing to use strings or other more complex types.
/// This improves memory and run-time performance.
/// 
/// The [id::IdManager] struct can be used to validate ID usage
/// at initialization.
pub mod id;

/// Provides functionality for procedural text generation.
pub mod text;

/// Provides traits and types for managing entities, actions, and events.
pub mod entity;
