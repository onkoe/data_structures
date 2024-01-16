//! # Linked List

use core::fmt::Debug;
use std::{borrow::BorrowMut, ops::DerefMut};
use thiserror::Error;

// TODO: do the much easier array implementation
// TODO: then, do the raw pointer unsafe nonsense
// TODO: finally, the interior mutability option. kinda like Box but also, no

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
    /// Creates a new `Node`.
    pub fn new(data: T) -> Self {
        Self { data, next: None }
    }

    /// Clones out the data from the node.
    pub fn data(&self) -> T {
        self.data.to_owned()
    }

    /// Replaces a node's data with `data`.
    pub fn set_data(&mut self, data: T) {
        self.data = data;
    }

    /// Sets a node's child to be the given `Node`.
    pub fn set_next_node(&mut self, node: Node<T>) {
        self.next = Some(Box::new(node));
    }

    /// Clones out the next node.
    pub fn next_node(&mut self) -> Option<Node<T>> {
        self.next.to_owned().map(|n| *n)
    }
    }
}

#[derive(Debug, Clone, PartialEq, PartialOrd)]

pub struct LinkedList<T: PartialEq + PartialOrd + Clone + Debug> {
    head: Option<Node<T>>,
}

impl<T: PartialEq + PartialOrd + Clone + Debug> LinkedList<T> {
    /// Creates a new linked list, given some head.
    /// `head` will define what type, `T`, the list will hold.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let list = LinkedList::new(123_i64);
    ///
    /// assert!(list.head().is_some());
    /// ```
    pub fn new(head: T) -> Self {
        Self {
            head: Some(Node::new(head)),
        }
    }

    /// Creates an empty linked list.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let list = LinkedList::<i32>::new_empty();
    ///
    /// assert_eq!(list.len(), 0);
    /// ```
    pub fn new_empty() -> Self {
        Self { head: None }
    }

    /// Changes `head` to be another node.
    ///
    /// WARNING: this drops ALL other nodes unless you manually save the rest
    /// of the list.
    ///
    /// ```
    /// # use data_structures::linked_list::{LinkedList, Node};
    /// # t().unwrap();
    /// #
    /// # fn t() -> Option<()> {
    /// let mut list = LinkedList::new("old head");
    /// list.set_head(Node::new("new head"));
    ///
    /// assert_eq!(list.head()?.data(), "new head");
    /// # Some(())
    /// # }
    /// ```
    pub fn set_head(&mut self, head: Node<T>) {
        self.head = Some(head);
    }

    /// Returns the current head node of the list.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// # t().unwrap();
    /// #
    /// # fn t() -> Option<()> {
    /// let list = LinkedList::new("hi");
    ///
    /// assert_eq!(list.head()?.data(), "hi");
    /// # Some(()) }
    /// ```
    pub fn head(&self) -> &Option<Node<T>> {
        &self.head
    }

    /// Return the node at the given position, if that position is valid.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// # t().unwrap();
    /// #
    /// # fn t() -> Option<()> {
    /// let list = LinkedList::new(0)
    ///     .to_add(1)
    ///     .to_add(2)
    ///     .to_add(3);
    ///
    /// assert_eq!(list.at(4)?.data, 3);
    /// # Some(()) }
    /// ```
    fn at(&self, position: usize) -> Option<Node<T>> {
        // TODO
        None
    }

    /// Returns the tail node, if such a node exists.
    /// Please note that head can also be tail!
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// # t().unwrap();
    /// #
    /// # fn t() -> Option<()> {
    /// let mut list = LinkedList::new(0_usize);
    /// for i in 1..=5 {
    ///     list.push(i);
    /// }
    ///
    /// assert_eq!(list.tail()?.data(), 5);
    /// # Some(())
    /// # }
    /// ```
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
    ///     list.push(0_u8);
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

    /// Checks to see if the linked list is empty.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let mut list = LinkedList::new("farts")
    ///     .to_push("one")
    ///     .to_push("two")
    ///     .to_push("three");
    ///
    /// assert!(!list.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.head.is_none()
    }

    /// Returns the first node in the list to have the given key.
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let list = LinkedList::new(0_u8)
    ///     .to_push(1_u8)
    ///     .to_push(2_u8)
    ///     .to_push(3_u8)
    ///     // etc...
    ///     .to_push(50_u8);
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

    /// Adds a new node to the back of the list.

    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let mut list = LinkedList::new(0_u8);
    /// list.push(1_u8);
    /// list.push(2_u8);
    /// list.push(3_u8);
    ///
    /// let tail = list.tail().unwrap();
    /// assert_eq!(tail.data(), 3_u8);
    /// ```
    pub fn push(&mut self, data: T) {
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

    /// Adds a new node to the back of the list, consuming self.
    /// Good for builder-like notation.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// let list = LinkedList::new(0_u8)
    ///     .to_push(1_u8)
    ///     .to_push(2_u8)
    ///     .to_push(3_u8);
    ///
    /// let tail = list.tail().unwrap();
    /// assert_eq!(tail.data(), 3_u8);
    /// ```
    pub fn to_push(mut self, data: T) -> Self {
        self.push(data);
        self
    }

    /// Inserts an element at a given position.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// # fn main() -> anyhow::Result<()> {
    /// let mut list = LinkedList::new("first");
    ///
    /// list.insert("second", 1)?;
    ///
    /// list.insert("third", 2)?;
    /// list.insert("fourth", 1)?;
    /// assert!(list.insert("wrong", 8).is_err());
    /// assert!(list.insert("also wrong", 5).is_err());
    /// list.insert("fifth", 4)?;
    ///
    /// let v = list.
    /// # Ok(()) }
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

    /// Inserts an element at a given position, consuming self.
    /// Good for builder-like notation.
    ///
    /// ```
    /// # use data_structures::linked_list::LinkedList;
    /// #
    /// # fn main() -> anyhow::Result<()> {
    /// let mut list = LinkedList::new("first")
    ///     .to_insert("second", 0)?
    ///     .to_insert("third", 2)?;
    ///
    /// assert!(list.to_insert("fourth", 4).is_err());
    /// # // TODO: use `.to_vec()` here in an `assert!()` when we get it!
    /// # Ok(()) }
    /// ```
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
    ///     .to_push(0_u8)
    ///     .to_push(0_u8)
    ///     .to_push(0_u8);
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

        assert_eq!(list.head().to_owned().unwrap().data(), 99_u8);
    }
}
