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
}
