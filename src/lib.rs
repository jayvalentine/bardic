#![deny(missing_docs)]

//! Bardic provides functionality for creating procedural narrative generators.
//! This includes:
//! 
//! * Text generation
//! * Entity management

/// Provides a way to manage and reference unique IDs for
/// entities in the system.
pub mod id;

/// Provides functionality for procedural text generation.
pub mod text;
