theory MyList

imports Main

begin

datatype 'a list = Nil | Cons 'a "'a list"

fun append :: "'a list => 'a list => 'a list" where
  "append Nil ys = ys" |
  "append (Cons x xs) ys = Cons x (append xs ys)"

fun reverse :: "'a list => 'a list" where
  "reverse Nil = Nil" |
  "reverse (Cons x xs) = append (reverse xs) (Cons x Nil)"

value "reverse (Cons false (Cons true Nil))" 

lemma append_nil [simp]:
  "append xs Nil = xs" (is "?P xs")
proof (induct xs)
  show "?P Nil" by simp
next
  fix x xs
  assume "?P xs"
  then show "?P (Cons x xs)" by simp
qed

lemma append_cons [simp]:
  "append xs (Cons y ys) = append xs (append (Cons y Nil) ys)" (is "?P xs")
proof (induct xs)
  show "?P Nil" by simp
next
  fix x xs
  assume "?P xs"
  then show "?P (Cons x xs)" by simp
qed

theorem reverse_reverse:
  "reverse (reverse xs) = xs" (is "?P xs")
proof (induct xs)
  show "?P Nil" by simp
next
  fix x xs
  assume "?P xs"
  then show "?P (Cons x xs)" by simp
qed

lemma reverse_append [simp]:
  "reverse (append xs ys) = append (reverse ys) (reverse xs)" (is "?P xs")
proof (induct xs)
  show "?P Nil" by simp 
next
  fix x xs
  assume "?P xs"
  then show "?P (Cons x xs)" by simp
qed

end