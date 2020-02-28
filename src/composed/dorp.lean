import .basic 
import ..category.lawful
open category (renaming monad → my_monad)

namespace composed

class dorp_constructor (m n : Type → Type) : Type 1 :=
(dorp : ∀{α : Type}, compose m n (m α) → compose m n α)

private def dorp.join {m n : Type → Type}
  [premonad m] [my_monad n] [dorp_constructor m n]
  (α : Type) : (compose m n) (compose m n α) → compose m n α
:= -- map_m join_m . dorp
begin
  intro mnmn,
  apply map.fixed m (join.fixed n),
  apply dorp_constructor.dorp,
  exact mnmn,
end

instance dorp.monad {m n : Type → Type}
  [premonad m] [my_monad n] [dorp_constructor m n]
  : my_monad (compose m n) := 
{ join := dorp.join, }

instance dorp.lawful {m n : Type → Type} [my_monad m] [my_monad n]
  [category.is_lawful_monad m] [category.is_lawful_monad n]
  [dorp_constructor m n]
  : category.is_lawful_monad (compose m n) :=
{ map_id := sorry,
  map_comp := sorry,
  unit_map := sorry,
  join_seq_map := sorry,
  join_unit := sorry,
  join_map_unit := sorry,
  join_map_join := sorry, }

end composed