theory MyNat

imports Main

begin

fun sum_up_to_of_fun :: "(nat => nat) => nat => nat" where
  "sum_up_to_of_fun f 0 = f 0" |
  "sum_up_to_of_fun f (Suc n) = f (n + 1) + sum_up_to_of_fun f n"

theorem sum_formula :
  "2 * sum_up_to_of_fun id n = n * (n + 1)"
proof (induction n)
  case 0 show ?case by simp
  case (Suc _) thus ?case by simp
qed

lemma exists_bigger_nat_0 :
  "\<forall> x :: nat. \<exists> y. y > x"
proof
  fix x :: nat
  let "?P y" = "y > x"
  have "?P (x + 1)" by simp
  thus "\<exists> y. ?P y" ..
qed

lemma exists_bigger_nat_1 :
  fixes x :: nat
  obtains y where "y > x"
proof
  show "x + 1 > x" by simp
qed

end