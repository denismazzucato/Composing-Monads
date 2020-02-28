import .basic
import ...category.lawful -- TODO: is there a better way to do it?

namespace maybe
#check category.functor.map

-- TODO: add a tactic to resolve this automatically

protected lemma map_id : ∀(α : Type),
  (category.functor.map id : maybe α → maybe α) = id :=
begin
  intro α,
  apply funext,
  intro x,
  cases x ; simp,
end

protected lemma map_comp : ∀(α β γ : Type) (f : γ → β) (g : α → γ),
  map f ∘ map g = (map (f ∘ g) : maybe α → maybe β) :=
begin
  intros α β γ f g,
  apply funext,
  intro x,
  cases x ; simp,
end

protected lemma unit_map : ∀(α β : Type) (f : α → β),
  unit ∘ f = map f ∘ (unit : α → maybe α) :=
begin
  intros α β f,
  apply funext,
  simp,
end

protected lemma join_seq_map : ∀(α β : Type) (f : α → β),
  join ∘ map (map f) = map f ∘ (join : maybe (maybe α) → maybe α) :=
begin
  intros α β f,
  apply funext,
  intro x,
  cases x ; simp,
end

protected lemma join_unit : ∀(α : Type),
  join ∘ unit = (id : maybe α → maybe α) :=
begin
  intro α,
  apply funext,
  simp,
end

protected lemma join_map_unit : ∀(α : Type), 
  join ∘ map unit = (id : maybe α → maybe α) :=
begin
  intro α,
  apply funext,
  intro x,
  cases x ; simp,
end

protected lemma join_map_join : ∀(α : Type),
  join ∘ map join = (join ∘ join : maybe (maybe (maybe α)) → maybe α) :=
begin
  intro α,
  apply funext,
  intro x,
  cases x ; simp,
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