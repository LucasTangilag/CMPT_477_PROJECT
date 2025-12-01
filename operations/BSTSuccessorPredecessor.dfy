include "../predicates/BSTPredicates.dfy"
include "../types/Tree.dfy"
include "../utils/Lemmas.dfy"

module BSTSuccessorPredecessor {
    import T = TreeModule
    import U = Utils
    import Pred = BSTPredicates
    import L = Lemmas

    method successor(t: T.Tree, root: T.Tree) returns (s: int, hasSucc: bool)
        requires t != T.Null
        requires Pred.in_BST(root, t.value)
        requires Pred.isBST(root)
        ensures Pred.isBST(root)
        ensures Pred.in_BST(root, t.value)
        ensures hasSucc ==> (t.right != T.Null ==> s == T.min_value_in_tree(t.right))
    {
        match t
        case Node(_, v, r, p) =>

            if r != T.Null {
                s := T.min_value_in_tree(r);
                hasSucc := true;
                return;
            }

            var curr := t;
            var par := p;

            while par != T.Null && curr == match par case Node(_,_,r2,_) => r2
                decreases par
            {
                curr := par;
                match par
                case Node(_,_,_,pp) => par := pp;
            }

            if par == T.Null {
                hasSucc := false;
                s := v; 
            } else {
                match par
                case Node(_, pv, _, _) =>
                    s := pv;
                    hasSucc := true;
            }
    }

    method predecessor(t: T.Tree, root: T.Tree) returns (pval: int, hasPred: bool)
        requires t != T.Null
        requires Pred.in_BST(root, t.value)
        requires Pred.isBST(root)
        ensures hasPred ==> (t.left != T.Null ==> pval == T.max_value_in_tree(t.left))
    {
        match t
        case Node(l, v, r, parent) =>

            // CASE 1: predecessor is in left subtree
            if l != T.Null {
                pval := T.max_value_in_tree(l);
                hasPred := true;
                return;
            }

            // CASE 2: walk up until we find a parent where we came from the right
            var curr := t;
            var par := parent;

            while par != T.Null && curr == match par case Node(l2, _, _, _) => l2
                decreases par
            {
                curr := par;
                match par
                case Node(_, _, _, pp) => par := pp;
            }

            if par == T.Null {
                // no predecessor exists
                hasPred := false;
                pval := v;  
            } else {
                match par
                case Node(_, pv, _, _) =>
                    pval := pv;
                    hasPred := true;
            }
  }
}