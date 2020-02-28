import .lawful
import ..utility

namespace to_std_monad

@[simp]
def join_to_bind {m : Type → Type} [category.monad m] (α β : Type) (x : m α)
  (f : α → m β) : m β := category.monad.join (category.functor.map f x)

instance {m : Type → Type} [category.monad m] : monad m :=
{ map := λα β, category.functor.map,
  pure := λα , category.premonad.unit,
  bind := join_to_bind, }

protected def id_map {m : Type → Type} [category.monad m] 
  [category.is_lawful_monad m] (α : Type) (x : m α) : id <$> x = x :=
by apply reverse_funext; apply category.is_lawful_functor.map_id

protected def pure_bind {m : Type → Type} [category.monad m] 
  [category.is_lawful_monad m] (α β : Type) (x : α) (f : α → m β) :
  pure x >>= f = f x :=
by simp[pure, bind, (category.unit_map f x).symm, (category.join_unit (f x))]

protected def bind_assoc {m : Type → Type} [category.monad m]
  [category.is_lawful_monad m] (α β γ : Type) (x : m α)
  (f : α → m β) (g : β → m γ) : x >>= f >>= g = x >>= λ (x : α), f x >>= g :=
begin
  simp[
    pure, 
    bind,
    (category.join_seq_map g (category.functor.map f x)).symm,
    (category.map_comp
      (λz, category.monad.join (category.functor.map g z))
      f
      x
    ).symm,
    (category.join_map_join
      (category.functor.map
        (category.functor.map g)
        (category.functor.map f x)
      )
    ).symm,
    (category.map_comp
      category.monad.join (category.functor.map g) (category.functor.map f x)
    ).symm
  ],
end

protected def bind_pure_comp_eq_map {m : Type → Type} [category.monad m]
  [category.is_lawful_monad m] (α β : Type) (f : α → β) (x : m α)
  : x >>= pure ∘ f = f <$> x :=
begin
  simp[
    functor.map,
    pure,
    bind,
    function.comp,
    (category.map_comp category.premonad.unit f x).symm,
    category.join_map_unit (category.functor.map f x)
  ],
end

instance {m : Type → Type} [category.monad m] [category.is_lawful_monad m] 
  : is_lawful_monad m :=
{ id_map := to_std_monad.id_map,
  pure_bind := to_std_monad.pure_bind,
  bind_assoc := to_std_monad.bind_assoc, 
  -- this one cannot be auto inferred from control_laws_tac
  bind_pure_comp_eq_map := to_std_monad.bind_pure_comp_eq_map, }

end to_std_monad

namespace from_std_monad

@[simp]
def bind_to_join {m : Type → Type} [monad m] (α : Type) : m (m α) → m α := mjoin

instance {m : Type → Type} [monad m] : category.monad m :=
{ map := λα β, functor.map,
  unit := λα, has_pure.pure,
  join := bind_to_join, }

instance {m : Type → Type} [monad m] [is_lawful_monad m] 
  : category.is_lawful_monad m := 
{ map_id := sorry,
  map_comp := sorry,
  unit_map := sorry,
  join_seq_map := sorry,
  join_unit := sorry,
  join_map_unit := sorry,
  join_map_join := sorry, }

end from_std_monad
