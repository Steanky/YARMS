use regex::{Regex, Replacer};
use std::borrow::Cow;

///
/// Extension methods for [`Regex`].
pub(crate) trait RegexExt {
    ///
    /// Replaces any matches in the input string, as if by [`Regex::replace_all`].
    ///
    /// If `input` would have been left unchanged, it is returned as-is. Otherwise, a new string is
    /// returned with the replacements having been applied.
    fn replace_all_owned(&self, input: String, rep: impl Replacer) -> String;
}

impl RegexExt for Regex {
    fn replace_all_owned(&self, input: String, rep: impl Replacer) -> String {
        match self.replace_all(&input, rep) {
            Cow::Borrowed(_) => input,
            Cow::Owned(string) => string,
        }
    }
}
