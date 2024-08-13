theory BinaryTree

imports Main

begin

datatype 'a tree
  = Empty
  | Parent "'a tree" "'a" "'a tree"

fun tree_to_list :: "'a tree => 'a list"
where
  "tree_to_list Empty = []" |
  "tree_to_list (Parent left x right) =
    tree_to_list left @ [x] @ tree_to_list right" 

abbreviation tree_to_set :: "'a tree => 'a set"
where
  "tree_to_set \<equiv> set \<circ> tree_to_list"

abbreviation is_ordered :: "int tree => bool"
where
  "is_ordered \<equiv> sorted \<circ> tree_to_list"

function insert_ordered :: "int => int tree => int tree"
where
  insert_empty : "insert_ordered x Empty = Parent Empty x Empty" |
  insert_leq :
    "x \<le> y \<Longrightarrow>
      insert_ordered x (Parent left y right) =
      Parent (insert_ordered x left) y right" |
  insert_gt :
    "x > y \<Longrightarrow>
      insert_ordered x (Parent left y right) =
      Parent left y (insert_ordered x right)"

apply (metis not_le_imp_less surjective_pairing tree_to_list.cases)
by simp_all

termination sorry

thm insert_ordered.induct

lemma tree_to_set_insert_ordered :
  "tree_to_set (insert_ordered x t) = {x} \<union> tree_to_set t"
  apply (induction rule: insert_ordered.induct)
  by simp_all

end