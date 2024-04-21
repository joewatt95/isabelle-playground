theory MyList

imports Main

begin

datatype 'a list
  = Nil
  | Cons 'a "'a list"

fun append :: "'a list => 'a list => 'a list" where
  "append Nil ys = ys" |
  "append (Cons x xs) ys = Cons x (append xs ys)"

fun reverse :: "'a list => 'a list" where
  "reverse Nil = Nil" |
  "reverse (Cons x xs) = append (reverse xs) (Cons x Nil)"

value "reverse (Cons false (Cons true Nil))" 

lemma append_nil [simp] :
  "append xs Nil = xs"
proof (induction xs)
  case Nil show ?case by simp
  case (Cons _ _) thus ?case by simp
qed

lemma append_cons [simp] :
  "append xs (Cons y ys) = append xs (append (Cons y Nil) ys)"
proof (induction xs)
  case Nil show ?case by simp
  case (Cons _ _) thus ?case by simp
qed

theorem reverse_reverse :
  "reverse (reverse xs) = xs"
proof (induction xs)
  case Nil show ?case by simp
  case (Cons _ _) thus ?case by simp
qed

lemma reverse_append [simp] :
  "reverse (append xs ys) = append (reverse ys) (reverse xs)" (is "?P xs")
proof (induction xs)
  case Nil show ?case by simp 
  case (Cons _ _) thus ?case by simp
qed

fun sum :: "nat list => nat" where
  "sum Nil = 0" |
  "sum (Cons x xs) = x + sum xs"

fun sum_tailrec :: "nat list => nat => nat" where
  "sum_tailrec Nil acc = acc" |
  "sum_tailrec (Cons x xs) acc = sum_tailrec xs (x + acc)"

lemma plus_sum_tailrec_eq_sum_tailrec_plus [simp] :
  "sum_tailrec xs (x + acc) = x + sum_tailrec xs acc"
proof (induction xs arbitrary: acc)
  case Nil show ?case by simp
  case (Cons _ _) thus ?case by smt
qed

theorem sum_eq_sum_tailrec :
  "acc + sum xs = sum_tailrec xs acc"
proof (induction xs)
  case Nil show ?case by simp
  case (Cons _ _) thus ?case by simp
qed

end