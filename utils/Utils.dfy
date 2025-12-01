include "../types/Tree.dfy"
include "../predicates/BSTPredicates.dfy"

module Utils {
    import T = TreeModule
    import Pred = BSTPredicates
    
    function max_value_in_tree(t: T.Tree): int
        requires t != T.Null
        
    {
        match t
            case Node(_, v, r_child, _) => 
                if r_child == T.Null then
                    v
                else 
                    max_value_in_tree(r_child)
    }

    // Helper find minimum element of t
    function min_value_in_tree(t: T.Tree): int
        requires t != T.Null
    {
        match t
            case Node(l_child, v, _, _) => 
                if l_child == T.Null then
                    v
                else 
                    min_value_in_tree(l_child)
                
    }

    //Helper that gets all values in a tree as a set
    function tree_values(t: T.Tree): multiset<int>
    {
        match t
        case Null => multiset{}
        case Node(l, v, r, _) =>
            multiset{v} + tree_values(l) + tree_values(r)
    }

    // Mathematical definition of inorder traversal (for reasoning)
    // : produce a sequence in inorder traversal order
    function inorder_traversal_seq(t: T.Tree): seq<int>
        requires Pred.isBST_for_traversal(t)
        decreases t
    {
        match t
        case Null => []
        case Node(l, v, r, _) =>
            inorder_traversal_seq(l) + [v] + inorder_traversal_seq(r)
    }
}