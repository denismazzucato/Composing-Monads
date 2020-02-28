import .functor

namespace category

class premonad (m : Type → Type) extends functor m :=
(unit {} : ∀{α : Type}, α → m α)
export category.premonad (unit)

def unit.fixed {α  : Type} (m : Type → Type) [premonad m]
: α → m α := @premonad.unit m _ α

end category