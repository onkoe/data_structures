//! # Linked List

use core::fmt::Debug;
use std::{borrow::BorrowMut, ops::DerefMut};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum LinkedListError {
    #[error("New elements can only be inserted up to `len + 1` elements off the list.")]
    ElementInsertionOffTheList,
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]
pub struct Node<T: PartialEq + PartialOrd + Clone + Debug> {
    data: T,
    next: Option<Box<Node<T>>>,
}

impl<T: PartialEq + PartialOrd + Clone + Debug> Node<T> {
    pub fn new(data: T) -> Self {
        Self { data, next: None }
    }

    pub fn data(&self) -> T {
        self.data.clone()
    }

    pub fn set_data(&mut self, data: T) {
        self.data = data;
    }

    pub fn set_next_node(&mut self, node: Node<T>) {
        self.next = Some(Box::new(node));
    }

    pub fn next_node(&mut self) -> Option<Node<T>> {
        self.next.clone().map(|n| *n)
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]

pub struct LinkedList<T: PartialEq + PartialOrd + Clone + Debug> {
    head: Option<Node<T>>,
}

impl<T: PartialEq + PartialOrd + Clone + Debug> LinkedList<T> {
    pub fn new(head: T) -> Self {
        Self {
            head: Some(Node::new(head)),
        }
    }

    pub fn set_head(&mut self, head: Node<T>) {
        self.head = Some(head);
    }

    pub fn head(&self) -> Option<Node<T>> {
        self.head.clone()
    }

    ///
    /// ```
    /// ```
    fn at(&self, position: usize) -> Option<Node<T>> {
        // TODO
        None
    }

    pub fn tail(&self) -> Option<Node<T>> {
        let mut node = &self.head.clone()?;

        while let Some(ref next_node) = node.next {
            node = next_node.as_ref();
        }

        Some(node.clone())
    }

    /// Returns the length of the linked list, counting head.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let mut list = LinkedList::new(0_u8);
    /// for _ in 0..99 {
    ///     list.append(0_u8);
    /// }
    ///
    /// assert_eq!(list.len(), 100);
    /// ```
    pub fn len(&self) -> usize {
        match &self.head {
            Some(h) => {
                let mut node = h;
                let mut counter: usize = 1;

                while let Some(ref next_node) = node.next {
                    node = next_node;
                    counter += 1;
                }

                counter
            }
            None => 0,
        }
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the first node in the list to have the given key.
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let list = LinkedList::new(0_u8)
    ///     .to_append(1_u8)
    ///     .to_append(2_u8)
    ///     .to_append(3_u8)
    ///     // etc...
    ///     .to_append(50_u8);
    ///
    /// assert!(list.get(50_u8).is_some());
    /// ```
    pub fn get<K: PartialEq<T>>(&self, key: K) -> Option<Node<T>> {
        if let Some(head) = self.head.clone() {
            let mut current_node = head;

            loop {
                if key == current_node.data() {
                    return Some(current_node.clone());
                }

                match current_node.next_node() {
                    Some(n) => current_node = n,
                    None => {
                        return None;
                    }
                }
            }
        } else {
            None
        }
    }

    /// Appends a new node to the back of the list.
    ///
    pub fn append(&mut self, data: T) {
        if let Some(ref mut h) = self.head {
            let mut current_node = h;

            loop {
                // if there's a node here, loop again
                if let Some(ref mut next_node) = current_node.next {
                    current_node = next_node;
                // otherwise, stick down the element
                } else {
                    current_node.set_next_node(Node::new(data.clone()));
                    break;
                }
            }
        }
    }

    /// Appends a new node to the back of the list, consuming self.
    /// Good for builder-like notation.
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let list = LinkedList::new(0_u8)
    ///     .to_append(1_u8)
    ///     .to_append(2_u8)
    ///     .to_append(3_u8);
    ///
    /// let tail = list.tail().unwrap();
    /// assert_eq!(tail.data(), 3_u8);
    /// ```
    pub fn to_append(mut self, data: T) -> Self {
        self.append(data);
        self
    }

    /// Inserts an element at a given position.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let mut list = LinkedList::new(0_u8);
    ///
    /// list.insert(29, 1);
    /// ```
    pub fn insert(&mut self, data: T, position: usize) -> Result<(), LinkedListError> {
        const ERR: LinkedListError = LinkedListError::ElementInsertionOffTheList;

        // disallow inserts that are off the list
        if position > self.len() {
            return Err(ERR);
        }

        if let Some(ref mut h) = self.head {
            let mut current_node = h;

            for _ in 0..position {
                let potential_next = &mut current_node.next;

                let next = potential_next.as_mut().ok_or(ERR)?.deref_mut();

                current_node = next;
            }

            // we're at the insertion point. let 'er rip
            let mut new_node = Node::new(data);

            if let Some(next) = current_node.next_node() {
                new_node.set_next_node(next);
            }

            current_node.set_next_node(new_node);
        } else {
            return Err(ERR);
        }
        Ok(())
    }

    pub fn to_insert(mut self, data: T, position: usize) -> Result<Self, LinkedListError> {
        self.insert(data, position)?;
        Ok(self)
    }

    /// Chops off the head of the linked list, leaving it completely empty.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let mut list = LinkedList::new(23_u8)
    ///     .to_append(0_u8)
    ///     .to_append(0_u8)
    ///     .to_append(0_u8);
    ///
    /// list.clear();
    ///
    /// assert_eq!(list.len(), 0);
    /// ```
    pub fn clear(&mut self) {
        self.head = None;
    }
}

// TODO
impl<T: PartialEq + PartialOrd + Clone + Debug> Iterator for LinkedList<T> {
    type Item = Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        todo!()
    }
}

#[cfg(test)]
mod tests {
    use super::LinkedList;

    #[test]
    fn insert_at_head() {
        let mut list = LinkedList::new(4_u8);
        list.insert(23_u8, 0).unwrap();
        list.insert(99_u8, 0).unwrap();

        assert_eq!(list.head().unwrap().data(), 4_u8);
    }
}