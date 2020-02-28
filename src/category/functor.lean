namespace category


class functor (m : Type → Type) : Type 1 :=
(map : ∀{α β : Type}, (α → β) → m α → m β)
export category.functor (map)

def map.fixed {α β : Type} (m : Type → Type) [functor m]
: (α → β) → m α → m β := @functor.map m _ α β

end category