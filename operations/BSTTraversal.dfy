include "../predicates/BSTPredicates.dfy"
include "../types/Tree.dfy"
include "../utils/Lemmas.dfy"
include "../utils/Utils.dfy"

module BSTTraversal {
    import T = TreeModule
    import U = Utils
    import Pred = BSTPredicates
    import L = Lemmas

    // Implementation of inorder traversal
    // : left subtree -> current node -> right subtree
    method inorder_traversal(t: T.Tree) returns (result: seq<int>)
        requires Pred.isBST_for_traversal(t) // valid BST
        // 1. all values in result exist in tree
        ensures forall i :: 0 <= i < |result| ==> result[i] in T.tree_values(t)
        // 2. result size equals tree size (no missing or extra tree values)
        ensures |result| == |T.tree_values(t)|
        // 3. inorder traversal's result is sorted
        ensures Pred.is_sorted(result)
        // 4. inorder traversal's result matches the mathematical function
        ensures result == U.inorder_traversal_seq(t)
        decreases t
    {
        match t
        case Null =>
            result := [];
        case Node(l, v, r, _) => 
            var left_result := inorder_traversal(l);
            var right_result := inorder_traversal(r);
            result := left_result + [v] + right_result;

            L.inorder_is_sorted(t);
            assert result == U.inorder_traversal_seq(t);
    }

    // Implementation of preorder traversal
    // : root node -> left subtree -> right subtree
    method preorder_traversal(t: T.Tree) returns (result: seq<int>)
        requires Pred.isBST_for_traversal(t)
        // 1. all values in result exists in tree
        ensures forall i :: 0 <= i < |result| ==> result[i] in T.tree_values(t)
        // 2. result size equals tree size (no missing or extra tree values)
        ensures |result| == |T.tree_values(t)|
        decreases t
    {
        match t
        case Null =>
            result := [];
        case Node(l, v, r, _) =>
            var left_result := preorder_traversal(l);
            var right_result := preorder_traversal(r);
            result := [v] + left_result + right_result;
    }

    // Implementation of postorder traversal
    // : left subtree -> right subtree -> root node
    method postorder_traversal(t: T.Tree) returns (result: seq<int>)
        requires Pred.isBST_for_traversal(t)
        // 1. all values in result exist in tree
        ensures forall i :: 0 <= i < |result| ==> result[i] in T.tree_values(t)
        // 2. result size equals tree size (no missing or extra tree values)
        ensures |result| == |T.tree_values(t)|
        decreases t
    {
        match t
        case Null =>
            result := [];
        case Node(l, v, r, _) =>
            var left_result := postorder_traversal(l);
            var right_result := postorder_traversal(r);
            result := left_result + right_result + [v];
    }
}
