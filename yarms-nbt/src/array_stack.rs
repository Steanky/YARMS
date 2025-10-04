///
/// An extremely simple array-based stack.
///
/// Since it's array-based, it won't perform heap allocations.
pub(crate) struct ArrayStack<T, const N: usize> {
    storage: [Option<T>; N],
    len: usize,
}

impl<T, const N: usize> ArrayStack<T, N> {
    pub(crate) fn new() -> ArrayStack<T, N> {
        ArrayStack {
            storage: [const { None }; N],
            len: 0,
        }
    }

    pub(crate) fn push(&mut self, element: T) -> bool {
        let next = self.len;

        if let Some(slot) = self.storage.get_mut(next) {
            *slot = Some(element);
            self.len += 1;
            true
        } else {
            false
        }
    }

    pub(crate) fn peek_mut(&mut self) -> Option<&mut T> {
        let next = self.len;
        if next == 0 {
            return None;
        }

        if let Some(slot) = self.storage.get_mut(next - 1) {
            slot.as_mut()
        } else {
            None
        }
    }

    pub(crate) fn pop(&mut self) -> Option<T> {
        let next = self.len;
        if next == 0 {
            return None;
        }

        if let Some(slot) = self.storage.get_mut(next - 1) {
            self.len -= 1;
            slot.take()
        } else {
            None
        }
    }
}
