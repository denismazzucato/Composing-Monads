import .inv

namespace category

lemma natural_join_doesnt_exists : ∀(x y : type),
  ¬ rmn (m $ n $ m $ n x) (m $ n x) :=
begin
  intros x y h,
  have h_not_inv : ¬ inv (m $ n $ m $ n x) (m $ n x) := 
  begin
    intro h,
    cases h,
    { have h_red_len : reduced_len (m (n x)) < reduced_len (m (n (m (n x)))) :=
      begin
        simp,
        rw add_comm _ (1 + (1 + len (reduce (n x)))),
        rw add_comm _ (len (reduce (n x))),
        apply nat.succ_lt_succ,
        rw add_comm,
        apply nat.lt_succ_of_lt,
        apply nat.lt_succ_self,
      end,
      simp at *,
      apply not_le_of_gt h_red_len,
      assumption, },
    { simp at *, assumption, },
  end,
  apply not_inv_imply_not_rmn h_not_inv,
  assumption,
end

end category