include "../types/Tree.dfy"
module BSTPredicates {
    import T = TreeModule

    // True iff all values in t are < bound
    predicate all_less_than(t: T.Tree, bound: int)
    {
      match t
      case Null => true
      case Node(l, v, r, _) =>
        v < bound && all_less_than(l, bound) && all_less_than(r, bound)
    }

    // True iff all values in t are > bound
    predicate all_greater_than(t: T.Tree, bound: int)
    {
      match t
      case Null => true
      case Node(l, v, r, _) =>
        v > bound && all_greater_than(l, bound) && all_greater_than(r, bound)
    }

    // searches and verifies if search_val is in t
    predicate in_BST(t: T.Tree, search_val: int)
    {
        match t
            case Null => false
            case Node(l, node_val, r, _) =>
                if node_val == search_val then
                    true
                else if search_val < node_val then
                    in_BST(l, search_val)
                else
                    in_BST(r, search_val)
    }

    // ensures that all BST properties are satsified
    predicate isBST(t: T.Tree)
    {
        match t
            case Null => true
            case Node(l_child,v,r_child, _) => 
                isBST(l_child) 
                && isBST(r_child) 
                && if (t.parent != T.Null) then (t == t.parent.left ==> t.value < t.parent.value) && (t == t.parent.right ==> t.value > t.parent.value) else true
                && (l_child != T.Null ==> all_less_than(l_child, v))
                && (r_child != T.Null ==> all_greater_than(r_child, v))
    }

    predicate is_sorted(s: seq<int>)
    {
        forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
    }


    predicate isBST_for_traversal(t: T.Tree)
    {
        match t
            case Null => true
            case Node(l_child, v, r_child, _) =>
                isBST_for_traversal(l_child)
                && isBST_for_traversal(r_child)
                && all_less_than(l_child, v)
                && all_greater_than(r_child, v)
    }

    // Check if all elements in input sequence are less than bound
    predicate seq_all_less_than(s: seq<int>, bound: int)
    {
        forall i :: 0 <= i < |s| ==> s[i] < bound
    }

    // Check if all elements in input sequence are greater than bound
    predicate seq_all_greater_than(s: seq<int>, bound: int)
    {
        forall i :: 0 <= i < |s| ==> s[i] > bound
    }
}
