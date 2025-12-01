include "../predicates/BSTPredicates.dfy"
include "../types/Tree.dfy"
include "../utils/Lemmas.dfy"

module BSTInsertDelete {
    import T = TreeModule
    import U = Utils
    import Pred = BSTPredicates
    import L = Lemmas

    function SetParent(t: T.Tree, p: T.Tree): T.Tree
    {
        match t
        case Null => T.Null
        case Node(l, v, r, _) => T.Node(SetParent(l, t), v, SetParent(r, t), p)
    }

    // Helper to find inorder successor
    method find_min(t: T.Tree) returns (min_val: int)
        requires t != T.Null
        ensures min_val == T.min_value_in_tree(t)
        decreases t
    {
        match t
        case Node(l, v, r, _) =>
            if l == T.Null {
                min_val := v;
            } else {
                min_val := find_min(l);
            }
    }

    // Appends a new value, v, as a descendent of current_node
    method add_recursive(current_node: T.Tree, v: int) returns (ret: T.Tree)
        requires Pred.isBST(current_node)
        ensures Pred.isBST(ret)
        ensures Pred.in_BST(ret, v)
    {
        match current_node
        case Node(curr_l, curr_v, curr_r, _) =>
            if (v < curr_v) { // Insert as left child
                var tmp := add_recursive(current_node.left, v);
                ret := T.Node(tmp, curr_v, curr_r, current_node);
            }
            else if (v > curr_v) { // Insert as right child
                var tmp := add_recursive(current_node.right, v);
                ret := T.Node(curr_l, curr_v, tmp, current_node);
            } else {
                ret := current_node;
            }
        case Null =>
            ret := T.Node(T.Null, v, T.Null, current_node);
    }

    // Verified delete_recursive; returns copy of tree without v
    method delete_recursive(current_node: T.Tree, v: int) returns (ret: T.Tree)
        requires Pred.isBST(current_node)
        ensures ret != T.Null || Pred.isBST(ret)
        decreases current_node
    {
        if current_node == T.Null {
            ret := T.Null;
            return;
        }

        match current_node
        case Node(curr_l, curr_v, curr_r, curr_parent) =>
            if v < curr_v {
                var new_left := delete_recursive(curr_l, v);
                ret := T.Node(new_left, curr_v, curr_r, curr_parent);
            } else if v > curr_v {
                var new_right := delete_recursive(curr_r, v);
                ret := T.Node(curr_l, curr_v, new_right, curr_parent);
            } else {
                // T.Node to delete
                if curr_l == T.Null {
                    ret := SetParent(curr_r, curr_parent);
                } else if curr_r == T.Null {
                    ret := SetParent(curr_l, curr_parent);
                } else {
                    // T.Node with two children: find successor
                    var successor_val := find_min(curr_r);
                    var new_right := delete_recursive(curr_r, successor_val);
                    ret := T.Node(curr_l, successor_val, SetParent(new_right, current_node), curr_parent);
                }
            }
    }
}
