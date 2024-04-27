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

inductive
  even :: "nat => bool" and
  odd :: "nat => bool"
where
  even_zero : "even 0" |
  odd_of_even : "even n \<Longrightarrow> odd (n + 1)" | 
  even_of_odd : "odd n \<Longrightarrow> even (n + 1)"

abbreviation even' :: "nat => bool" where
  "even' n \<equiv> \<exists> k. n = 2 * k"

abbreviation odd' :: "nat => bool" where
  "odd' n \<equiv> \<exists> k. n = 2 * k + 1"

lemma even_odd_of_even'_odd' :
  shows
    "even' n = even n" and
    "odd' n = odd n"
proof (induction n)
  case 0 {
    case 2 
    \<comment> \<open>sledgehammer\<close>
    show ?case by (simp add: odd.simps) 
  next
    case 1
    \<comment> \<open>sledgehammer\<close>
    show ?case by (simp add: even_odd.even_zero)
  }
next
  case (Suc _) {
    case 1
    \<comment> \<open>sledgehammer\<close>
    show ?case by (
      metis
      Suc.IH(2) Suc_eq_plus1 add_right_imp_eq dvd_triv_left even.simps
      even_Suc nat.simps(3) oddE
    ) 
  next
    case 2
    \<comment> \<open>sledgehammer\<close>
    show ?case by (simp add: Suc.IH(1) odd.simps)
  }
qed

end