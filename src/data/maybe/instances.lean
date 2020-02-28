import .basic
import ...category.lawful

namespace maybe

protected lemma map_id : ∀(α : Type),
  (category.functor.map id : maybe α → maybe α) = id :=
begin
  intro α,
  apply funext,
  intro x,
  cases x ; simp[category.functor.map],
end

protected lemma map_comp : ∀(α β γ : Type) (f : γ → β) (g : α → γ),
  category.functor.map f ∘ category.functor.map g
  = (category.functor.map (f ∘ g) : maybe α → maybe β) :=
begin
  intros α β γ f g,
  apply funext,
  intro x,
  cases x ; simp[category.functor.map],
end

protected lemma unit_map : ∀(α β : Type) (f : α → β),
  category.premonad.unit ∘ f
  = category.functor.map f ∘ (category.premonad.unit : α → maybe α) :=
begin
  intros α β f,
  apply funext,
  simp[category.functor.map, category.premonad.unit],
end

protected lemma join_seq_map : ∀(α β : Type) (f : α → β),
  category.monad.join ∘ category.functor.map (category.functor.map f)
  = category.functor.map f ∘ (category.monad.join 
    : maybe (maybe α) → maybe α) :=
begin
  intros α β f,
  apply funext,
  intro x,
  cases x ;
  simp[category.functor.map, category.premonad.unit, category.monad.join],
end

protected lemma join_unit : ∀(α : Type),
  category.monad.join ∘ category.premonad.unit = (id : maybe α → maybe α) :=
begin
  intro α,
  apply funext,
  simp[category.functor.map, category.premonad.unit, category.monad.join],
end

protected lemma join_map_unit : ∀(α : Type), 
  category.monad.join ∘ category.functor.map category.premonad.unit
  = (id : maybe α → maybe α) :=
begin
  intro α,
  apply funext,
  intro x,
  cases x ; 
  simp[category.functor.map, category.premonad.unit, category.monad.join],
end

protected lemma join_map_join : ∀(α : Type),
  category.monad.join ∘ category.functor.map category.monad.join
  = (category.monad.join ∘ category.monad.join
    : maybe (maybe (maybe α)) → maybe α) :=
begin
  intro α,
  apply funext,
  intro x,
  cases x ; 
  simp[category.functor.map, category.premonad.unit, category.monad.join],
end

instance : category.is_lawful_functor maybe :=
{ map_id := maybe.map_id,
  map_comp := maybe.map_comp, }

instance : category.is_lawful_premonad maybe :=
{ unit_map := maybe.unit_map, }

instance : category.is_lawful_monad maybe :=
{ join_seq_map := maybe.join_seq_map,
  join_unit := maybe.join_unit,
  join_map_unit := maybe.join_map_unit,
  join_map_join := maybe.join_map_join, }

end maybe