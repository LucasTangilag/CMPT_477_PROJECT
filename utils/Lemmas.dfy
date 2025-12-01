include "../types/Tree.dfy"
include "../predicates/BSTPredicates.dfy"
include "../utils/Utils.dfy"

import T = TreeModule
import Pred = BSTPredicates
import U = Utils

// Helps Dafny verify inorder_is_sorted
// : prove that if all tree values are less than bound, then so is the inorder sequence (connect tree properties to sequence properties)
lemma all_less_than_to_seq(t: T.Tree, bound: int)
    requires Pred.isBST_for_traversal(t)
    requires Pred.all_less_than(t, bound)
    ensures Pred.seq_all_less_than(U.inorder_traversal_seq(t), bound)
    decreases t
{
    match t
    case Null => {}
    case Node(l, v, r, _) =>
        all_less_than_to_seq(l, bound);
        all_less_than_to_seq(r, bound);
}

// Helps Dafny verify inorder_is_sorted
// : prove that if all tree values are greater than bound, then so is the inorder sequence (connect tree properties to sequence properties)
lemma all_greater_than_to_seq(t: T.Tree, bound: int)
    requires Pred.isBST_for_traversal(t)
    requires Pred.all_greater_than(t, bound)
    ensures Pred.seq_all_greater_than(U.inorder_traversal_seq(t), bound)
    decreases t
{
    match t
    case Null => {}
    case Node(l, v, r, _) =>
        all_greater_than_to_seq(l, bound);
        all_greater_than_to_seq(r, bound);

}

// Helps Dafny verify inorder_traversal
// : prove that inorder traversal gives sorted output for valid BST
lemma inorder_is_sorted(t: T.Tree)
    requires Pred.isBST_for_traversal(t)
    ensures Pred.is_sorted(U.inorder_traversal_seq(t))
    decreases t
{
    match t
    case Null => {}
    case Node(l, v, r, _) =>
        inorder_is_sorted(l);
        inorder_is_sorted(r);

        assert Pred.all_less_than(l, v);
        assert Pred.all_greater_than(r, v);

        all_less_than_to_seq(l, v);
        all_greater_than_to_seq(r, v);
}
