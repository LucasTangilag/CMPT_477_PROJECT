module TreeModule {
  datatype Tree =
      Null
    | Node(left: Tree, value: int, right: Tree, parent: Tree)

    function height(t: Tree): int
        ensures t == Null ==> height(t) == 0
        ensures t != Null ==> height(t) > 0
        decreases t
    {
        match t
        case Null => 0
        case Node(l, _, r, _) => 1 + if height(l) > height(r) then height(l) else height(r)
    }

    //Helper that gets all values in a tree as a set
    function tree_values(t: Tree): multiset<int>
    {
        match t
        case Null => multiset{}
        case Node(l, v, r, _) =>
            multiset{v} + tree_values(l) + tree_values(r)
    }

    // Helper find minimum element of t
    function min_value_in_tree(t: Tree): int
        requires t != Null
    {
        match t
            case Node(l_child, v, _, _) => 
                if l_child == Null then
                    v
                else 
                    min_value_in_tree(l_child)
                
    }
}
