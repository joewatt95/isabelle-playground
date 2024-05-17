theory MyNat

imports Main

begin

fun sumUpToOfFun :: "(nat => nat) => nat => nat"
where
  "sumUpToOfFun f 0 = f 0" |
  "sumUpToOfFun f (Suc n) = f (n + 1) + sumUpToOfFun f n"

theorem sum_formula :
  "2 * sumUpToOfFun id n = n * (n + 1)"
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

abbreviation even' :: "nat => bool"
where
  "even' n \<equiv> \<exists> k. n = 2 * k"

abbreviation odd' :: "nat => bool"
where
  "odd' n \<equiv> \<exists> k. n = 2 * k + 1"

lemma even_odd_of_even'_odd' :
  shows
    even_of_even' : "even' n \<Longrightarrow> even n" and
    odd_of_odd' : "odd' n \<Longrightarrow> odd n"
proof (induction n)
  case 0
  {
    case 1
    assume "even' 0"
    thus ?case by (simp add: even_odd.even_zero)
  next
    case 2
    assume "odd' 0"
    thus ?case by simp
  }
next
  case (Suc n)
  {
    case 1
    assume "even' (Suc n)"

    thus ?case when "odd' n" (is ?thesis)
      using Suc.IH(2) even_of_odd that by fastforce 

    obtain k where "n + 1 = 2 * k" by (metis "1" Suc_eq_plus1)
    hence "n = 2 * (k - 1) + 1" by simp
    thus ?thesis by blast
  next
    case 2
    assume "odd' (Suc n)"

    thus ?case when "even' n" (is ?thesis)
      using Suc.IH(1) odd_of_even that by fastforce

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
  thus "even' (m + 1)"
    by (metis ab_semigroup_add_class.add_ac(1) add.commute mult_2)
qed

theorem even_eq_even' :
  "even n = even' n"
  using even'_of_even even_of_even' by blast

theorem odd_or_even :
  "odd n \<or> even n"
proof (induction n)
  case 0
  thus ?case using even_zero by fastforce
next
  case (Suc n)
  assume "odd n \<or> even n"

  thus ?case
  proof
    assume "odd n"
    thus ?case using even_of_odd by fastforce
  next
    assume "even n"
    thus ?case using odd_of_even by fastforce
  qed
qed

corollary odd'_or_even' :
  "odd' n \<or> even' n"
  using odd_or_even odd'_of_odd even'_of_even by blast

inductive
  leq :: "nat => nat => bool"
where
  leq_self : "leq m m" |
  leq_succ_of_leq : "leq m n \<Longrightarrow> leq m (n + 1)"

abbreviation leq' :: "nat => nat => bool"
where
  "leq' m n \<equiv> \<exists> k. n = m + k"

lemma leq'_of_leq :
  "leq m n \<Longrightarrow> leq' m n"
proof (induction rule: leq.induct)
  case leq_self
  show ?case by simp
next
  case leq_succ_of_leq
  fix m n
  assume "leq m n" and "leq' m n"
  then obtain k where "n = m + k" by blast
  hence "n + 1 = m + (k + 1)" by simp
  thus "leq' m (n + 1)" by blast
qed

lemma leq_of_leq' :
  "leq' m n \<Longrightarrow> leq m n"
proof (induction n arbitrary: m rule: less_induct)
  case (less n)
  then obtain k where n_eq_m_plus_k : "n = m + k" by blast

  thus "leq m n"
  proof (cases k)
    case 0
    hence "n = m" by (simp add: n_eq_m_plus_k)
    thus ?thesis using leq_self by blast
  next
    case (Suc k')
    hence "n - 1 = m + k'" by (simp add: n_eq_m_plus_k)
    hence "leq m (n - 1)" by (simp add: Suc less.IH n_eq_m_plus_k)
    thus ?thesis using leq_succ_of_leq by blast
  qed
qed

theorem leq_eq_leq' :
  "leq m n = leq' m n"
  using leq_of_leq' leq'_of_leq by blast

end