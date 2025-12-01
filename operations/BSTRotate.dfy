include "../predicates/BSTPredicates.dfy"
include "../types/Tree.dfy"
include "../utils/Lemmas.dfy"
include "../utils/Utils.dfy"

module BSTRotate {
    import T = TreeModule
    import U = Utils
    import Pred = BSTPredicates
    import L = Lemmas

    // Left rotate x around its right child y
    //         x                           y
    //       /   \                       /   \
    //      A     y        ->           x     C
    //          /   \                 /   \
    //         B     C               A     B

    method left_rotate(x: T.Tree) returns (ret: T.Tree)
        requires x != T.Null && x.right != T.Null
        requires Pred.isBST(x)                
        ensures ret != T.Null
        ensures T.tree_values(ret) == T.tree_values(x) 
    {
        match x
        case Node(A, x_val, y, x_parent) =>
            match y
            case Node(B, y_val, C, y_parent) =>
                //build new x node with A and B as its children
                var new_x := T.Node(A, x_val, B, T.Null);
                //build new root node with new_x and C as its children
                ret := T.Node(new_x, y_val, C, x_parent);
    }

    // ROTATIONS
    // Right rotate y around its left child x
    //          y                         x
    //        /   \                     /   \
    //       x     C       ->           A     y
    //     /   \                           /   \
    //    A     B                         B     C
    
    method right_rotate(y: T.Tree) returns (ret: T.Tree)
        requires y != T.Null && y.left != T.Null
        requires Pred.isBST(y)             
        ensures ret != T.Null
        ensures T.tree_values(ret) == T.tree_values(y)  
    {
        match y
        case Node(x, y_val, C, y_parent) =>
            match x
            case Node(A, x_val, B, x_parent) =>
                //build new y node with B and C as its children
                var new_y := T.Node(B, y_val, C, T.Null);
                //build new root node with A and new_y as its children
                ret := T.Node(A, x_val, new_y, y_parent);
    }
}
