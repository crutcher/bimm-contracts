//! # SlotMap and Index
//!
//! Fast mutable maps with limited discrete key spaces.

use alloc::vec;
use alloc::vec::Vec;
use core::fmt::Debug;

///
#[derive(Debug)]
pub struct SlotIndex<'a> {
    /// The index of the slot in the SlotMap's storage.
    pub keys: &'a [&'a str],
}

impl<'a> SlotIndex<'a> {
    /// The number of slots in the index.
    pub fn slot_count(&self) -> usize {
        self.keys.len()
    }

    /// Compute the slot for a key.
    ///
    /// # Panics
    ///
    /// If the key is not in the index.
    pub fn to_slot(&self, key: &str) -> usize {
        for (i, k) in self.keys.iter().enumerate() {
            if *k == key {
                return i;
            }
        }
        panic!("Unknown key: {}", key)
    }
}

/// A slot-based map.
pub struct SlotMap<T>
where T: 'static + Debug + Clone
{
    /// The slots in the map.
    pub slots: Vec<Option<T>>
}

impl<T> SlotMap<T>
    where T: 'static + Debug + Clone {
    /// Create a new map with the given capacity.
    pub fn new_with_capacity(capacity: usize) -> Self {
        Self { slots: vec![None; capacity] }
    }

    /// Clear the map.
    pub fn clear(&mut self) {
        self.slots.fill(None);
    }

    /// Lookup a value in the map.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.slots.get(index).and_then(|x| x.as_ref())
    }

    /// Set a value in the map.
    pub fn set(&mut self, index: usize, value: T) {
        self.slots[index] = Some(value);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_slot_index() {
        static INDEX: SlotIndex<'static> = SlotIndex { keys: &["a", "b", "c"] };

        assert_eq!(INDEX.slot_count(), 3);

        assert_eq!(INDEX.to_slot("a"), 0);
        assert_eq!(INDEX.to_slot("b"), 1);
        assert_eq!(INDEX.to_slot("c"), 2);
    }

    #[test]
    #[should_panic(expected = "Unknown key: d")]
    fn test_slot_index_panic() {
        static INDEX: SlotIndex<'static> = SlotIndex { keys: &["a", "b", "c"] };

        INDEX.to_slot("d");
    }

    #[test]
    fn test_slot_map() {
        let mut map = SlotMap::new_with_capacity(3);
        map.set(0, 1);

        assert_eq!(map.get(0), Some(&1));
        assert_eq!(map.get(1), None);

        map.clear();

        assert_eq!(map.get(0), None);
    }
}