use super::{LinkedList, Node};
use core::fmt::Debug;

/// An iterator over a `LinkedList`.
#[derive(Debug, PartialEq, PartialOrd)]
pub struct LinkedListIterator<'a, T: PartialEq + PartialOrd + Clone + Debug> {
    pub(super) list: &'a LinkedList<T>,
    pub(super) current: Option<&'a Node<T>>,
}

impl<'a, T: PartialEq + PartialOrd + Clone + Debug> Iterator for LinkedListIterator<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let n = &self.current?.data;
        self.current = self.current?.next.as_deref();
        //self.current = self.current?.next.as_deref().and(|n: Node<T>| n.data);
        Some(n)
    }
}

/// An iterator over a `LinkedList` and its `Node`s.
#[derive(Debug, PartialEq, PartialOrd)]
pub struct LinkedListNodeIterator<'a, T: PartialEq + PartialOrd + Clone + Debug> {
    pub(super) list: &'a LinkedList<T>,
    pub(super) current: Option<&'a Node<T>>,
}

impl<'a, T: PartialEq + PartialOrd + Clone + Debug> Iterator for LinkedListNodeIterator<'a, T> {
    type Item = &'a Node<T>;

    fn next(&mut self) -> Option<Self::Item> {
        let n = self.current;
        self.current = self.current?.next.as_deref();
        n
    }
}

#[cfg(test)]
mod tests {
    use crate::linked_list::LinkedList;

    #[test]
    fn sanity_check() {
        let list = LinkedList::new(0)
            .to_push(1)
            .to_push(2)
            .to_push(3)
            .to_push(4)
            .to_push(5);

        let mut v = Vec::<i32>::new();

        for e in list.iter() {
            v.push(*e);
        }

        assert_eq!(v, vec![0, 1, 2, 3, 4, 5]);
    }

    #[test]
    fn empty() {
        let list = LinkedList::<i32>::new_empty();

        assert!(list.iter().collect::<Vec<&i32>>().is_empty());
    }
}
