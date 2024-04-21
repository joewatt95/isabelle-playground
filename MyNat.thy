theory MyNat

imports Main

begin

fun sum_up_to_of_fun :: "(nat => nat) => nat => nat" where
  "sum_up_to_of_fun f 0 = f 0" |
  "sum_up_to_of_fun f (Suc n) = f (n + 1) + (sum_up_to_of_fun f n)"

theorem sum_formula :
  "2 * sum_up_to_of_fun id n = n * (n + 1)"
proof (induction n)
  case 0 show ?case by simp
  case (Suc _) thus ?case by simp
qed

lemma exists_bigger_nat :
  "\<forall> x :: nat. \<exists> y. y > x"
proof
  fix x :: nat
  let "?P y" = "y > x"
  have "?P (x + 1)" by simp
  thus "\<exists> y. ?P y" by auto
qed

end