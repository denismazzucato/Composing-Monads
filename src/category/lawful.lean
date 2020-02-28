import .monad

namespace category

class is_lawful_functor (m : Type → Type) [functor m] : Prop :=
(map_id : ∀{α : Type}, map id = (id : m α → m α))
(map_comp : ∀{α β γ : Type} (f : γ → β) (g : α → γ),
  map f ∘ map g = (map (f ∘ g) : m α → m β))

class is_lawful_premonad (m : Type → Type) [premonad m]
  extends is_lawful_functor m :=
(unit_map : ∀{α β : Type} (f : α → β), unit ∘ f = map f ∘ (unit : α → m α))

class is_lawful_monad (m : Type → Type) [monad m]
  extends is_lawful_premonad m :=
(join_seq_map : ∀{α β : Type} (f : α → β),
  join ∘ map (map f) = map f ∘ (join : m (m α) → m α))
(join_unit : ∀{α : Type}, join ∘ unit = (id : m α → m α))
(join_map_unit : ∀{α : Type}, join ∘ map unit = (id : m α → m α))
(join_map_join : ∀{α : Type}, join ∘ map join = (join ∘ join :_ → m α))

lemma comp_to_app {α β γ : Type} {x : α} (f : β → γ) (g : α → β)
  : f (g x) = (f ∘ g) x := by simp

lemma map_comp {m : Type → Type} [functor m] [is_lawful_functor m] 
  {α β γ : Type} (f : γ → β) (g : α → γ) (x : m α)
  : map f (map g x) = map (λy, f (g y)) x :=
by rw [comp_to_app (map f) (map g), is_lawful_functor.map_comp]

lemma unit_map {m : Type → Type} [premonad m] [is_lawful_premonad m]
  {α β : Type} (f : α → β) (x : α) : unit (f x) = map f (unit x : m α) :=
by rw [comp_to_app unit f, is_lawful_premonad.unit_map]

lemma join_seq_map {m : Type → Type} [monad m] [is_lawful_monad m]
  {α β : Type} (f : α → β) (x : m (m α))
  : join (map (map f) x) = map f (join x) :=
by rw [comp_to_app join (map (map f)), is_lawful_monad.join_seq_map]

lemma join_unit {m : Type → Type} [monad m] [is_lawful_monad m]
  {α : Type} (x : m α) : join (unit x) = id x :=
by rw [comp_to_app join unit, is_lawful_monad.join_unit]

lemma join_map_unit {m : Type → Type} [monad m] [is_lawful_monad m]
  {α : Type} (x : m α) : join (map unit x) = id x :=
by rw [comp_to_app join (map unit), is_lawful_monad.join_map_unit]

lemma join_map_join {m : Type → Type} [monad m] [is_lawful_monad m]
  {α : Type} (x : m (m (m α))) : join (map join x) = join (join x) :=
by rw [comp_to_app join (map join), is_lawful_monad.join_map_join]

end category