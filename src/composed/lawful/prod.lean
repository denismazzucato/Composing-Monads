import ..prod
open category (renaming monad → my_monad) 
open composed (renaming prod_constructor.prod → my_prod)

namespace composed 

class is_lawful_prod (m n : Type → Type) [my_monad m] [premonad n]
  [prod_constructor m n] :=
(prod_map_map : ∀{α β : Type} (f : α → β), 
  my_prod ∘ map (map f) = map f ∘ (my_prod :_ → compose m n α))
(prod_unit : ∀{α : Type}, my_prod ∘ unit = (id : _ → compose m n α))
(prod_map_unit : ∀{α : Type}, my_prod ∘ map unit = (unit : n α → compose m n α))
(prod_map_join : ∀{α : Type}, 
  my_prod ∘ map join = (join ∘ my_prod : _ → compose m n α))

protected def prod_from_monad {m n : Type → Type} [my_monad m] [my_monad n] 
  [my_monad (compose m n)] (α : Type) : n (compose m n α) → compose m n α :=
join ∘ unit.fixed m

instance {m n : Type → Type} [my_monad m] [my_monad n] [my_monad (compose m n)] 
  : prod_constructor m n := { prod := composed.prod_from_monad, }

end composed