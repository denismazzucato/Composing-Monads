lemma reverse_funext {α β : Type} (f g : α → β) (h : f = g) (x : α) : f x = g x 
:= by simp [h]

lemma not_congr_imply {a b : Prop} (h : a → b) : ¬b → ¬a := λ hb a, hb (h a) 

lemma le_of_add_one_of_lt {b c : ℕ} (h : b < c) : 1 + b ≤ c := 
begin
  cases h,
  simp,
  apply le_trans,
  simp[(≤)], assumption,
  apply nat.le_succ,
end

lemma le_of_lt_of_add_one {a b : ℕ} (h : a < b) : a ≤ b + 1 :=
begin
  cases h,
  simp[@nat.le.intro a _ 2],
  apply le_trans,
  apply nat.le_succ,
  apply le_trans,
  apply h_a,
  simp[@nat.le.intro h_b _ 2],
end