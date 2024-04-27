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
    "even' n \<Longrightarrow> even n" and
    "odd' n \<Longrightarrow>  odd n"
proof (induction n)
  case 0
  {
    case 1
    \<comment> \<open>sledgehammer\<close>
    show ?case by (simp add: even_odd.even_zero)
  next
    case 2
    \<comment> \<open>sledgehammer\<close>
    show ?case using "2" by auto
  }
next
  case (Suc n)
  {
    case 1
    \<comment> \<open>sledgehammer\<close>
    moreover obtain k where "n + 1 = 2 * k"
      using Suc_eq_plus1 calculation by presburger
    \<comment> \<open>sledgehammer\<close>
    moreover show ?case when "odd' n" (is ?thesis)
      using Suc.IH(2) Suc_eq_plus1 even_of_odd that by presburger 
    \<comment> \<open>sledgehammer\<close>
    moreover have "n = 2 * (k - 1) + 1" using calculation(2) by linarith
    ultimately show ?thesis by blast
  next
    case 2
    \<comment> \<open>sledgehammer\<close>
    moreover obtain k where "n + 1 = 2 * k + 1"
      using Suc_eq_plus1 calculation by presburger
    \<comment> \<open>sledgehammer\<close>
    moreover show ?case when "even' n" (is ?thesis)
      using Suc.IH(1) Suc_eq_plus1 odd_of_even that by presburger
    \<comment> \<open>sledgehammer\<close>
    moreover have "n = 2 * k" using calculation(2) by linarith
    ultimately show ?thesis by blast
  }
qed

lemma even'_odd'_of_even_odd :
  shows
    "even n \<Longrightarrow> even' n" and
    "odd n \<Longrightarrow> odd' n"
proof (induction rule: even_odd.inducts)
  case even_zero
  show ?case by simp
next
  case odd_of_even
  fix n assume "even n" and "even' n"
  then obtain k where "n = 2 * k" by blast
  thus "odd' (n + 1)" by simp
next
  case even_of_odd
  fix n assume "odd n" and "odd' n"
  then obtain k where "n = 2 * k + 1" by blast
  \<comment> \<open>sledgehammer\<close>
  thus "even' (n + 1)"
    by (metis ab_semigroup_add_class.add_ac(1) add.commute mult_2)
qed

theorem even_eq_even' :
  "even n = even' n"
  using even'_odd'_of_even_odd even_odd_of_even'_odd' by blast

theorem edd_eq_odd' :
  "odd n = odd' n"
  using even'_odd'_of_even_odd even_odd_of_even'_odd' by blast

end