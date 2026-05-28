import Mathlib.Data.List.Basic

namespace MembershipProject.Core

variable {α : Type*}

/--
Theorem: If two lists are definitionally constructed from a shared front prefix
and differ only by their last components, swapping those components reconstructs
the original lists in reverse order.
-/
theorem swap_last_is_definitional (front : List α) (x y : α) :
    let L1 := front ++ [x]
    let L2 := front ++ [y]
    (front ++ [y], front ++ [x]) = (L2, L1) := by
  rfl

end MembershipProject.Core
