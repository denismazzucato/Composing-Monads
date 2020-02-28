import .basic
import ..category.lawful
open category (renaming functor → my_functor) (renaming monad → my_monad)

namespace composed

protected lemma map_id {m n : Type → Type} [my_functor m] [my_functor n] 
  [category.is_lawful_functor m] [category.is_lawful_functor n] (α : Type) :
  map id = (id : compose m n α → compose m n α) :=
begin
  apply funext,
  intro x,
  simp[category.functor.map, composed.map, category.is_lawful_functor.map_id],
end

protected lemma map_comp {m n : Type → Type} [my_functor m] [my_functor n] 
  [category.is_lawful_functor m] [category.is_lawful_functor n]
  (α β γ : Type) (f : γ → β) (g : α → γ) :
  map f ∘ map g = (map (f ∘ g) : compose m n α → compose m n β) :=
begin
  apply funext,
  intro x,
  simp[category.functor.map, composed.map, category.is_lawful_functor.map_comp],
end

instance {m n : Type → Type} [my_functor m] [my_functor n]
  [category.is_lawful_functor m] [category.is_lawful_functor n]
  : category.is_lawful_functor (compose m n) :=
{ map_id := composed.map_id,
  map_comp := composed.map_comp, }

protected lemma unit_map {m n : Type → Type} [premonad m] [premonad n]
  [category.is_lawful_premonad m] [category.is_lawful_premonad n]
  (α β : Type) (f : α → β) :
  unit ∘ f = map f ∘ (unit : α → compose m n α) :=
begin 
  apply funext,
  intro x,
  simp[
    category.functor.map,
    category.premonad.unit,
    composed.map,
    composed.unit],
  simp[
    (category.unit_map
      (category.functor.map f)
      (category.premonad.unit x)
    ).symm,
    (category.unit_map f x).symm],
end  

instance {m n : Type → Type} [premonad m] [premonad n]
  [category.is_lawful_premonad m] [category.is_lawful_premonad n]
  : category.is_lawful_premonad (compose m n) :=
{ unit_map := composed.unit_map, }

end composed