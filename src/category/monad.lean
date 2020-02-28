import .premonad

namespace category

class monad (m : Type → Type) extends premonad m :=
(join : ∀{α : Type}, m (m α) → m α)
export category.monad (join)

def join.fixed {α  : Type} (m : Type → Type) [monad m]
: m (m α) → m α := @monad.join m _ α

end category