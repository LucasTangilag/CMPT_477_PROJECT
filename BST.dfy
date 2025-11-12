// CMPT 477
// Aarham Haider, Sumandeep Kaur, Nayoung Kim, Lucas Tangilag, Natalie Woods

// JAVA REFERENCE: https://github.com/dtfiedler/java-binary-tree/blob/master/src/BinaryTree.java

/*
    TODO: DOUBLE CHECK IMPLEMENTATION & VERIFICATION FOR INSERT 
    TODO: IMPLEMENT & VERIFY FIND FUNCTIONS
    TODO: IMPLEMENT & VERIFY DELETE FUNCTION
    TODO: IMPLEMENT & VERIFY TREE TRAVERSALS

    Something that could maybe help with the above tasks is to also create a function that traverses the tree and outputs the values, in sorted order, in an array.
    This could make it easier to verify
*/

datatype Tree = Null | Node(left: Tree, value: int, right: Tree, parent: Tree)

class BST{
    var root: Tree

    constructor(r: Tree)
        ensures isBST(root)
    {
       root := r;
       new; 
       if (!isBST(r)) {
        root := Null; // Constructs valid tree, on the condition that paramter r is also valid
       }
    }

    // Used as helper in isBST
    function max_value_in_tree(t: Tree): int
        requires t != Null
        
    {
        match t
            case Node(_, v, r_child, _) => 
                if r_child == Null then
                    v
                else 
                    max_value_in_tree(r_child)
    }


    // Used as helper in isBST
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

    predicate in_BST(t: Tree, search_val: int)
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

    // Returns true iff 't' contains search_val
    method value_in_tree(t: Tree, search_val: int) returns (ret: bool)
        requires t != Null
        ensures ret ==> in_BST(t, search_val) // ENSURE THAT THE VALUE IS IN THE TREE IFF THE PREDICATE HOLDS
        decreases t
    {
        match t
            case Node(l_child, node_val, r_child, _) => 
                if (node_val == search_val) {
                    ret := true;
                } else if (search_val < node_val) { // LESS THAN CASE
                    if (l_child == Null) {
                        ret := false;
                    } else {
                        ret := value_in_tree(l_child, search_val);
                    }
                } else { // GREATER THAN CASE
                    if (r_child == Null) {
                        ret := false;
                    } else {
                        ret := value_in_tree(r_child, search_val);
                    }
                }
    }

    // True iff all values in t are < bound
    predicate all_less_than(t: Tree, bound: int)
    {
      match t
      case Null => true
      case Node(l, v, r, _) =>
        v < bound && all_less_than(l, bound) && all_less_than(r, bound)
    }

    // True iff all values in t are > bound
    predicate all_greater_than(t: Tree, bound: int)
    {
      match t
      case Null => true
      case Node(l, v, r, _) =>
        v > bound && all_greater_than(l, bound) && all_greater_than(r, bound)
    }

    // TODO: ENSURE THAT THESE CONDITIONS ACTUALLY DO ENFORCE THE ORDERING PROPERTY (because I'm actually not even sure if it does)
    predicate isBST(t: Tree)
    {
        match t
            case Null => true
            case Node(l_child,v,r_child, _) => 
                isBST(l_child) 
                && isBST(r_child) 
                // && (l_child != Null ==> max_value_in_tree(l_child) <= t.value) 
                // && (r_child != Null ==> min_value_in_tree(r_child) >= t.value)
                && if (t.parent != Null) then (t == t.parent.left ==> t.value < t.parent.value) && (t == t.parent.right ==> t.value > t.parent.value) else true
                && (l_child != Null ==> all_less_than(l_child, v))
                && (r_child != Null ==> all_greater_than(r_child, v))
    }

    // Appends a new value, v, as a descendent of current_node
    // TODO : ENSURE PROPER ORDERING AS POST CONDITION
    // TODO : ADD ANY OTHER APPROPRIATE VERIFICATION CONDITIONS 
    method add_recursive(current_node: Tree, v: int) returns (ret: Tree)
        requires isBST(current_node)
        ensures isBST(ret)
        ensures in_BST(ret, v)
    {
        match current_node
        case Node(curr_l, curr_v, curr_r, _) =>
            if (v < curr_v) { // Insert as left child
                var tmp := add_recursive(current_node.left, v);
                ret := Node(tmp, curr_v, curr_r, current_node);
            }
            else if (v > curr_v) { // Insert as right child
                var tmp := add_recursive(current_node.right, v);
                ret := Node(curr_l, curr_v, tmp, current_node);
            } else {
                ret := current_node;
            }
        case Null =>
            ret := Node(Null, v, Null, current_node);
    }

    // So far, we just assume that we have a valid structure, and then that insertion doesn't break our structure
    // TODO: FIND A WAY TO VERIFY THAT, FROM THE VERY BEGINNING, THE BST PROPERTIES HOLD
    method insert(v: int)
        modifies this
        requires isBST(this.root)
        ensures isBST(this.root)

    {
        this.root := add_recursive(this.root, v);
    }
}