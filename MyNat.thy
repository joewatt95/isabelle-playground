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
  obtains y :: nat where "y > x"
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
    even_of_even' : "even' n \<Longrightarrow> even n" and
    odd_of_odd' : "odd' n \<Longrightarrow> odd n"
proof (induction n)
  case 0
  {
    case 1 assume "even' 0"
    \<comment> \<open>sledgehammer\<close>
    thus ?case by (simp add: even_odd.even_zero)
  next
    case 2 assume "odd' 0"
    thus ?case by simp
  }
next
  case (Suc n)
  {
    case 1 assume "even' (Suc n)"
    \<comment> \<open>sledgehammer\<close>
    thus ?case when "odd' n" (is ?thesis)
      using Suc.IH(2) even_of_odd that by fastforce 
    \<comment> \<open>sledgehammer\<close>
    obtain k where "n + 1 = 2 * k" by (metis "1" Suc_eq_plus1)
    hence "n = 2 * (k - 1) + 1" by simp
    thus ?thesis by blast
  next
    case 2 assume "odd' (Suc n)"
    \<comment> \<open>sledgehammer\<close>
    thus ?case when "even' n" (is ?thesis)
      using Suc.IH(1) odd_of_even that by fastforce
    \<comment> \<open>sledgehammer\<close>
    obtain k where "n + 1 = 2 * k + 1" by (metis "2" Suc_eq_plus1)
    hence "n = 2 * k" by simp
    thus ?thesis by blast
  }
qed

lemma even'_odd'_of_even_odd :
  shows
    even'_of_even : "even n \<Longrightarrow> even' n" and
    odd'_of_odd : "odd n \<Longrightarrow> odd' n"
proof (induction rule: even_odd.inducts)
  case even_zero
  thus ?case by simp
next
  case odd_of_even
  fix m assume "even m" and "even' m"
  then obtain k where "m = 2 * k" by blast
  thus "odd' (m + 1)" by simp
next
  case even_of_odd
  fix m assume "odd m" and "odd' m"
  then obtain k where "m = 2 * k + 1" by blast
  \<comment> \<open>sledgehammer\<close>
  thus "even' (m + 1)"
    by (metis ab_semigroup_add_class.add_ac(1) add.commute mult_2)
qed

theorem even_eq_even' :
  "even n = even' n"
  using even'_of_even even_of_even' by blast

theorem edd_eq_odd' :
  "odd n = odd' n"
  using odd'_of_odd odd_of_odd' by blast

theorem odd_or_even :
  "odd n \<or> even n"
proof (induction n)
  case 0
  thus ?case using even_odd.even_zero by fastforce
next
  case (Suc n)
  thus ?case
  proof
    assume "even n"
    thus ?case using even_odd.odd_of_even by fastforce
  next
    assume "odd n"
    thus ?case using even_odd.even_of_odd by fastforce
  qed
qed

corollary odd'_or_even' :
  "odd' n \<or> even' n"
  using odd_or_even odd'_of_odd even'_of_even by blast

end