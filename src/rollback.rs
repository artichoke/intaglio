use crate::internal::Interned;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum GuardState {
    Armed,
    Defused,
}

/// Roll back the last push to an interner backing vector if unwinding occurs
/// before the corresponding map insert succeeds.
pub(crate) struct VecEntryRollbackGuard<'a, T: 'static + ?Sized> {
    vec: &'a mut Vec<Interned<T>>,
    state: GuardState,
}

impl<'a, T> VecEntryRollbackGuard<'a, T>
where
    T: ?Sized,
{
    #[inline]
    pub(crate) fn new(vec: &'a mut Vec<Interned<T>>, value: Interned<T>) -> Self {
        vec.push(value);
        Self {
            vec,
            state: GuardState::Armed,
        }
    }

    #[inline]
    pub(crate) fn last(&self) -> &Interned<T> {
        debug_assert!(!self.vec.is_empty());
        // SAFETY: `VecEntryRollbackGuard::new` always pushes one element.
        unsafe { self.vec.last().unwrap_unchecked() }
    }

    #[inline]
    pub(crate) fn defuse(mut self) {
        self.state = GuardState::Defused;
    }
}

impl<T> Drop for VecEntryRollbackGuard<'_, T>
where
    T: ?Sized,
{
    fn drop(&mut self) {
        match self.state {
            GuardState::Armed => {
                drop(self.vec.pop());
            }
            GuardState::Defused => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use std::borrow::Cow;

    use super::VecEntryRollbackGuard;
    use crate::internal::Interned;

    #[test]
    fn armed_guard_rolls_back_last_push() {
        let mut vec = vec![Interned::from(Cow::Borrowed("existing"))];

        {
            let guard = VecEntryRollbackGuard::new(&mut vec, Interned::from(Cow::Borrowed("new")));

            assert_eq!(guard.last().as_slice(), "new");
        }

        assert_eq!(vec.len(), 1);
        assert_eq!(vec[0].as_slice(), "existing");
    }

    #[test]
    fn defused_guard_keeps_pushed_value() {
        let mut vec = Vec::new();

        {
            let guard =
                VecEntryRollbackGuard::new(&mut vec, Interned::from(Cow::Borrowed("persist")));

            assert_eq!(guard.last().as_slice(), "persist");
            guard.defuse();
        }

        assert_eq!(vec.len(), 1);
        assert_eq!(vec[0].as_slice(), "persist");
    }
}
