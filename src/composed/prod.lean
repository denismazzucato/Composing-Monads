import .basic 
import ..category.lawful
open category (renaming monad → my_monad)

namespace composed

class prod_constructor (m n : Type → Type) : Type 1 :=
(prod : ∀{α : Type}, n (compose m n α) → compose m n α)

private def prod.join {m n : Type → Type}
  [my_monad m] [premonad n] [prod_constructor m n]
  (α : Type) : (compose m n) (compose m n α) → compose m n α
:= -- join_m . map_m prod
begin
  intro mnmn,
  apply join.fixed m,
  apply map.fixed m prod_constructor.prod,
  exact mnmn,
  assumption,
end

instance prod.monad {m n : Type → Type}
  [my_monad m] [premonad n] [prod_constructor m n]
  : my_monad (compose m n) := 
{ join := prod.join, }

instance prod.lawful {m n : Type → Type} [my_monad m] [my_monad n]
  [category.is_lawful_monad m] [category.is_lawful_monad n]
  [prod_constructor m n]
  : category.is_lawful_monad (compose m n) :=
{ map_id := sorry,
  map_comp := sorry,
  unit_map := sorry,
  join_seq_map := sorry,
  join_unit := sorry,
  join_map_unit := sorry,
  join_map_join := sorry, }

end composed