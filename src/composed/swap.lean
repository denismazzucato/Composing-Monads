import .basic 
import ..category.lawful
open category (renaming monad → my_monad)

namespace composed

class swap_constructor (m n : Type → Type) : Type 1 :=
(swap : ∀{α : Type}, compose n m α → compose m n α)

private def swap.join {m n : Type → Type}
  [my_monad m] [my_monad n] [swap_constructor m n]
  (α : Type) : compose m n (compose m n α) → compose m n α
:= -- join_m . map_m (map_m join_n . swap)
have h_map_join_swap : n (compose m n α) → m (n α) := 
begin
  intro nmn,
  apply map.fixed m (join.fixed n),
  apply swap_constructor.swap,
  exact nmn,
end,
begin
  intro mnmn,
  apply join.fixed m,
  apply map.fixed m h_map_join_swap,
  exact mnmn,
end

instance swap.monad {m n : Type → Type} [my_monad m] [my_monad n] 
  [swap_constructor m n] 
  : my_monad (compose m n) := 
{ join := swap.join, }

instance swap.lawful {m n : Type → Type} [my_monad m] [my_monad n]
  [category.is_lawful_monad m] [category.is_lawful_monad n]
  [swap_constructor m n]
  : category.is_lawful_monad (compose m n) :=
{ map_id := sorry,
  map_comp := sorry,
  unit_map := sorry,
  join_seq_map := sorry,
  join_unit := sorry,
  join_map_unit := sorry,
  join_map_join := sorry, }

end composed