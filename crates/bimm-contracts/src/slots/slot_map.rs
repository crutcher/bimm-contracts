//! # `SlotMap` and Index
//!
//! Fast mutable maps with limited discrete key spaces.

use core::fmt::Debug;

/// Key-To-Index Slot Mapping.
#[derive(Debug)]
pub struct SlotIndex<'a> {
    /// The index of the slot in the `SlotMap`'s storage.
    pub keys: &'a [&'a str],
}

impl<'a> SlotIndex<'a> {
    /// The number of slots in the index.
    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Compute the slot for a key.
    ///
    /// # Panics
    ///
    /// If the key is not in the index.
    pub fn slot(&self, key: &str) -> usize {
        for (i, k) in self.keys.iter().enumerate() {
            if *k == key {
                return i;
            }
        }
        panic!("Unknown key: {}", key)
    }

    /// Get the key for a slot.
    pub fn key(&self, slot: usize) -> &str {
        self.keys[slot]
    }
}

/// Readable slot bindings.
pub trait SlotBindings {
    /// Get a value in the map by slot.
    ///
    /// # Arguments
    ///
    /// * `slot`: the slot id.
    ///
    /// # Returns
    ///
    /// An `Option<isize>`.
    fn get_slot(&self, slot: usize) -> Option<isize>;
}

/// Mutable slot bindings.
pub trait MutableSlotBindings: SlotBindings {
    /// Set a value in the map by slot.
    ///
    /// # Arguments
    ///
    /// * `slot`: the slot id.
    /// * `value`: the new value.
    fn set_slot(&mut self, slot: usize, value: isize);
}

impl<const D: usize> SlotBindings for [Option<isize>; D] {
    fn get_slot(&self, slot: usize) -> Option<isize> {
        self[slot].clone()
    }
}
impl<const D: usize> MutableSlotBindings for [Option<isize>; D] {
    fn set_slot(&mut self, slot: usize, value: isize) {
        self[slot] = Some(value);
    }
}

impl SlotBindings for [Option<isize>] {
    fn get_slot(&self, slot: usize) -> Option<isize> {
        self[slot].clone()
    }
}
impl MutableSlotBindings for [Option<isize>] {
    fn set_slot(&mut self, slot: usize, value: isize) {
        self[slot] = Some(value);
    }
}

/// Overlay slots.
pub struct OverlaySlots<'a> {
    /// Backing slots.
    pub backing: &'a [Option<isize>],

    /// Overlay changes.
    pub overlay: &'a mut [Option<isize>],
}

impl<'a> SlotBindings for OverlaySlots<'a> {
    fn get_slot(&self, slot: usize) -> Option<isize> {
        self.overlay[slot].or_else(|| self.backing[slot])
    }
}

impl<'a> MutableSlotBindings for OverlaySlots<'a> {
    fn set_slot(&mut self, slot: usize, value: isize) {
        self.overlay[slot] = Some(value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slot_index() {
        static INDEX: SlotIndex<'static> = SlotIndex {
            keys: &["a", "b", "c"],
        };

        assert_eq!(INDEX.len(), 3);

        assert_eq!(INDEX.slot("a"), 0);
        assert_eq!(INDEX.slot("b"), 1);
        assert_eq!(INDEX.slot("c"), 2);
    }

    #[test]
    #[should_panic(expected = "Unknown key: d")]
    fn test_slot_index_panic() {
        static INDEX: SlotIndex<'static> = SlotIndex {
            keys: &["a", "b", "c"],
        };

        INDEX.slot("d");
    }
}
