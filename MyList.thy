theory MyList

imports Main

begin

datatype 'a list
  = Nil
  | Cons 'a "'a list"

fun append :: "'a list => 'a list => 'a list"
where
  appendNil : "append Nil ys = ys" |
  appendCons : "append (Cons x xs) ys = Cons x (append xs ys)"

fun reverse :: "'a list => 'a list"
where
  reverseNil : "reverse Nil = Nil" |
  reverseCons : "reverse (Cons x xs) = append (reverse xs) (Cons x Nil)"

value "reverse (Cons false (Cons true Nil))" 

lemma append_nil [simp] :
  "append xs Nil = xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons _ _)
  thus ?case by simp
qed

lemma append_cons [simp] :
  "append xs (Cons y ys) = append xs (append (Cons y Nil) ys)"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons _ _)
  thus ?case by simp
qed

theorem reverse_reverse [simp] :
  "reverse (reverse xs) = xs"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons _ _)
  thus ?case by simp
qed

lemma reverse_append [simp] :
  "reverse (append xs ys) = append (reverse ys) (reverse xs)"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons _ _)
  thus ?case by simp
qed

lemma test_auto_quickcheck_false :
  "reverse (append xs ys) = append (reverse xs) (reverse ys)"
  (* by sledgehammer [abduce = 1] *)
  oops

fun sum :: "nat list => nat"
where
  "sum Nil = 0" |
  "sum (Cons x xs) = x + sum xs"

fun sum_tailrec :: "nat list => nat => nat"
where
  "sum_tailrec Nil acc = acc" |
  "sum_tailrec (Cons x xs) acc = sum_tailrec xs (x + acc)"

lemma plus_sum_tailrec_eq_sum_tailrec_plus [simp] :
  "sum_tailrec xs (x + acc) = x + sum_tailrec xs acc"
proof (induction xs arbitrary: acc)
  case Nil
  show ?case by simp
next
  case (Cons _ _)
  thus ?case by (simp add: add.left_commute)
qed

theorem acc_sum_eq_sum_tailrec_acc :
  "acc + sum xs = sum_tailrec xs acc"
proof (induction xs)
  case Nil
  show ?case by simp
next
  case (Cons _ _)
  thus ?case by simp
qed

corollary sum_eq_sum_tail_rec :
  "sum xs = sum_tailrec xs 0"
  by (metis acc_sum_eq_sum_tailrec_acc add_0_left)

end