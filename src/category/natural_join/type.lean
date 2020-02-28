namespace category

inductive type : Type
| α : type
| m (t : type) : type
| n (t : type) : type
export type (α m n)

@[simp] def first_eq : type → type → Prop
| α     α     := true
| (m _) (m _) := true
| (n _) (n _) := true
| _     _     := false

@[simp] def first_neq (t₁ t₂ : type) : Prop :=
¬ first_eq t₁ t₂

@[simp] def reduce : type → type
| α := α
| (m $ m t) := reduce (m t)
| (n $ n t) := reduce (n t)
| (m t) := m $ reduce t
| (n t) := n $ reduce t

@[simp] def len : type → ℕ
| α := 1
| (m t) := 1 + len t
| (n t) := 1 + len t

@[simp] def reduced_len : type → ℕ := len ∘ reduce

--------------------------------------------------------------------------------
-- lemmas about inductive type 'type'
--------------------------------------------------------------------------------

lemma first_eq_same (x : type) : first_eq x x :=
by cases x; simp

lemma first_eq_trans (x y z : type) (hxy : first_eq x y) (hyz : first_eq y z) :
  first_eq x z :=
begin
  cases x ; cases y; cases z,
  repeat { simp *, },
  repeat { simp at hyz, simp at hxy, assumption, },
end

lemma first_neq_same (x : type) : ¬ first_neq x x :=
λh, by simp[first_eq_same x] at h; assumption

lemma len_lower_bound (x : type) : 1 ≤ len x :=
begin
cases x;
rw len,
repeat { 
  apply le_add_of_nonneg_right,
  apply nat.le.intro (zero_add (len x)), },
end

lemma len_lower_bound_zero (x : type) : 0 < len x :=
lt_of_lt_of_le zero_lt_one (len_lower_bound x)

lemma len_lower_bound_lt (x : type) (hx : x ≠ α) : 1 < len x :=
begin
  cases x,
  { apply false.elim, apply hx, simp, },
  repeat {
    simp[len],
    rw add_comm,
    apply lt_add_of_pos_right,
    cases x; simp[len],
    apply zero_lt_one,
    repeat {
      rw gt,
      rw nat.add_one,
      apply nat.zero_lt_succ, }, },
end

lemma reduce_neq_α (x : type) (hx : x ≠ α) : reduce x ≠ α :=
begin
  induction x,
  apply hx,
  repeat { cases x_t; simp[reduce, x_ih], },
end
 
lemma reduced_len_same (x : type) : reduced_len x ≤ reduced_len x := 
le_of_eq (by cases x ; simp)

lemma reduced_len_α (x : type) : reduced_len α ≤ reduced_len x :=
begin
  cases x,
  apply reduced_len_same,
  repeat { simp, apply len_lower_bound, },
end

lemma reduced_len_α_lt {x} (hx : x ≠ α) : reduced_len α < reduced_len x :=
begin
  cases x,
  { apply false.elim, apply hx, simp, },
  any_goals { cases x ; simp },
  { apply nat.lt.base, },
  { apply len_lower_bound_lt, simp[reduce_neq_α], },
  { apply lt_add_of_pos_right, 
    have h := len_lower_bound_lt (reduce _) (reduce_neq_α _ _),
    rw gt,
    apply lt_trans zero_lt_one h,
    simp, }, 
  { apply nat.lt.base, },
  { rw add_comm, apply lt_add_of_pos_left, apply len_lower_bound_zero, },
  { apply len_lower_bound_lt, apply reduce_neq_α, simp, }, 
end

end category