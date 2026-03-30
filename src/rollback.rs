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
    pub(crate) fn defuse(&mut self) {
        match self.state {
            GuardState::Armed => {
                self.state = GuardState::Defused;
            }
            GuardState::Defused => {
                unreachable!("VecEntryRollbackGuard defused more than once");
            }
        }
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
