///
/// Extension methods for iterators. Just used internally for convenience.
pub(crate) trait IteratorExt: Iterator {
    ///
    /// Joins an iterator of string-like elements into a single, newly-allocated string with each
    /// element separated by `sep`. Returns when the iterator returns `None` for the first time.
    ///
    /// Iterators that never return none should not be used with this method, as with other
    /// collector-type methods, because it will never return, and in this case may cause unbounded
    /// growth of memory usage.
    ///
    /// The returned string will only contain the separator string between consecutive entries in
    /// the iterator, it will not prepend/append the separator.
    ///
    /// If the iterator does not return any elements, the string will be empty. Its allocated
    /// capacity, if any, is undefined.
    fn join<S: AsRef<str>>(self, sep: S) -> String
    where
        Self::Item: AsRef<str>;
}

impl<Iter> IteratorExt for Iter
where
    Iter: Iterator,
{
    fn join<S: AsRef<str>>(self, sep: S) -> String
    where
        Self::Item: AsRef<str>,
    {
        join(self, sep)
    }
}

fn join<It, I, S>(mut iter: I, sep: S) -> String
where
    It: AsRef<str>,
    I: Iterator<Item = It>,
    S: AsRef<str>,
{
    let separator = sep.as_ref();

    let mut string = String::new();
    let mut first = true;
    loop {
        match iter.next() {
            None => return string,
            Some(item) => {
                if !first {
                    string.push_str(separator);
                }

                string.push_str(item.as_ref());
            }
        }

        first = false;
    }
}
