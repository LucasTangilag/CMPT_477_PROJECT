include "Tree.dfy"
module BSTPredicates {
    import TreeModule
    // True iff all values in t are < bound
    predicate all_less_than(t: TreeModule.Tree, bound: int)
    {
      match t
      case Null => true
      case Node(l, v, r, _) =>
        v < bound && all_less_than(l, bound) && all_less_than(r, bound)
    }

    // True iff all values in t are > bound
    predicate all_greater_than(t: TreeModule.Tree, bound: int)
    {
      match t
      case Null => true
      case Node(l, v, r, _) =>
        v > bound && all_greater_than(l, bound) && all_greater_than(r, bound)
    }

    // searches and verifies if search_val is in t
    predicate in_BST(t: TreeModule.Tree, search_val: int)
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
    predicate isBST(t: TreeModule.Tree)
    {
        match t
            case Null => true
            case Node(l_child,v,r_child, _) => 
                isBST(l_child) 
                && isBST(r_child) 
                && if (t.parent != TreeModule.Null) then (t == t.parent.left ==> t.value < t.parent.value) && (t == t.parent.right ==> t.value > t.parent.value) else true
                && (l_child != TreeModule.Null ==> all_less_than(l_child, v))
                && (r_child != TreeModule.Null ==> all_greater_than(r_child, v))
    }

    predicate is_sorted(s: seq<int>)
    {
        forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
    }
}
