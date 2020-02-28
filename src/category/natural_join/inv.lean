import .type
import ...utility

namespace category

inductive rmn : type → type → Prop
| r_id : ∀{α}, rmn α α
| comp {α β γ} (f : rmn γ β) (g : rmn α γ) : rmn α β
| map_m {α β} (f : rmn α β) : rmn (m α) (m β)
| map_n {α β} (f : rmn α β) : rmn (n α) (n β)
| unit_m : ∀{α}, rmn α (m α)
| unit_n : ∀{α}, rmn α (n α)
| join_m : ∀{α}, rmn (m $ m α) (m α)
| join_n : ∀{α}, rmn (n $ n α) (n α)
export rmn (r_id comp map_m map_n unit_m unit_n join_m join_n)

inductive inv : type → type → Prop
| eq {x y} :
  reduced_len x ≤ reduced_len y
  → first_eq x y
  → inv x y
| neq {x y} :
  reduced_len x < reduced_len y 
  → first_neq x y
  → inv x y

--------------------------------------------------------------------------------
-- lemmas about 'inv' and 'rmn'
--------------------------------------------------------------------------------

lemma inv_same (x : type) : inv x x :=
by cases x ; { apply inv.eq, apply reduced_len_same, apply first_eq_same, }

lemma inv_first_is_α (x : type) : inv α x :=
begin
  cases x,
  { apply inv_same, },
  repeat { 
    apply inv.neq,
    apply reduced_len_α_lt,
    simp,
    simp, },
end

lemma inv_last_is_α {x : type} (hx : x ≠ α) : ¬ inv x α :=
begin
  cases x ; intro hinv,
  { apply false.elim, apply hx, simp, },
  repeat { cases hinv,
    rw first_eq at hinv_a_1,
    assumption,
    simp at hinv_a,
    apply iff.elim_left (lt_iff_not_ge _ _) hinv_a,
    apply len_lower_bound, },
end

lemma inv_trans {x y z : type} (hxz : inv x z) (hzy : inv z y) : inv x y :=
begin
  cases x; cases y; cases z,
  any_goals { apply inv_first_is_α, },
  any_goals { apply false.elim, apply inv_last_is_α (by simp) hxz, },
  any_goals { apply false.elim, apply inv_last_is_α (by simp) hzy, },
  repeat { cases hxz ; cases hzy, },
  repeat { apply false.elim, simp at hzy_a_1, assumption, },
  repeat { apply false.elim, simp at hxz_a_1, assumption, }, 

  any_goals { apply inv.eq (le_trans hxz_a hzy_a), simp, },
  any_goals { apply inv.eq (le_of_lt $ lt_trans hxz_a hzy_a), simp, },
  any_goals { apply inv.neq (lt_of_le_of_lt hxz_a hzy_a), simp, },
  any_goals { apply inv.neq (lt_of_lt_of_le hxz_a hzy_a), simp, },
end

lemma rmn_inv_map_m {x y : type} (h : rmn x y) (ih : inv x y)
  : reduced_len (m x) ≤ reduced_len (m y) :=
begin
  cases ih ; cases x ; cases y,
  any_goals { simp, },

  repeat {apply false.elim, simp at ih_a_1, assumption, }, 
  any_goals { simp at ih_a, },

  { assumption, },
  { apply add_le_add_left, assumption, },
  { apply le_of_add_one_of_lt ih_a, },
  { apply add_le_add_left (le_of_lt ih_a), },
  { apply le_of_lt_of_add_one ih_a, },
  { rw add_comm, apply le_of_lt_of_add_one ih_a, },
  { apply add_le_add_left, apply le_of_lt ih_a, },
  { apply le_of_add_one_of_lt ih_a, },
end

lemma rmn_inv_map_n {x y : type} (h : rmn x y) (ih : inv x y)
  : reduced_len (n x) ≤ reduced_len (n y) :=
begin
  cases ih ; cases x ; cases y,
  any_goals { simp, },

  repeat { apply false.elim, simp at ih_a_1, assumption, }, 
  any_goals { simp at ih_a, },

  { apply add_le_add_left, assumption, },
  { assumption, },
  { apply add_le_add_left (le_of_lt ih_a), },
  { apply le_of_add_one_of_lt ih_a, },
  { apply add_le_add_left, apply le_of_lt ih_a, },
  { apply le_of_add_one_of_lt ih_a, },
  { apply le_of_lt_of_add_one ih_a, },
  { rw add_comm, apply le_of_lt_of_add_one ih_a, },
end

lemma rmn_inv : ∀{x y : type}, rmn x y → inv x y :=
begin
  intros x y h,
  induction h,
  case r_id : t { apply inv_same, },
  case comp : x y z hzy hxz ihzy ihxz { apply inv_trans ihxz ihzy, },
  case map_m : x y h ih { apply inv.eq, apply rmn_inv_map_m h ih, simp, },
  case map_n : x y h ih { apply inv.eq, apply rmn_inv_map_n h ih, simp, },
  case unit_m : x y {
    cases x,
    apply inv_first_is_α,
    { apply inv.eq ; simp, },
    apply inv.neq,
    { simp, rw add_comm,apply nat.lt.base, },
    { simp, },
  },
  case unit_n : x y h { 
    cases x,
    apply inv_first_is_α,
    apply inv.neq,
    { simp, rw add_comm, apply nat.lt.base, },
    { simp, },
    apply inv.eq ; simp,
  },
  case join_m : x y h { apply inv.eq ; simp, },
  case join_n : x y h { apply inv.eq ; simp, },
  end

lemma not_inv_imply_not_rmn : ∀{x y : type}, ¬ inv x y → ¬ rmn x y :=
λx y, not_congr_imply rmn_inv

end category