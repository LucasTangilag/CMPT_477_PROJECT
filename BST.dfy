// CMPT 477
// Aarham Haider, Sumandeep Kaur, Nayoung Kim, Lucas Tangilag, Natalie Woods

// JAVA REFERENCE: https://github.com/dtfiedler/java-binary-tree/blob/master/src/BinaryTree.java

/*
    TODO: DOUBLE CHECK LUCAS' IMPLEMENTATIONS FOR INSERT AND FIND, ENSURE VALIDITY HOLDS
    TODO: IMPLEMENT & VERIFY DELETE FUNCTION
    TODO: IMPLEMENT & VERIFY TREE TRAVERSALS
*/

datatype Tree = Null | Node(left: Tree, value: int, right: Tree)

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
            case Node(_, v, r_child) => 
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
            case Node(l_child, v, _) => 
                if l_child == Null then
                    v
                else 
                    min_value_in_tree(l_child)
                
    }

    // [Lucas]: Fixed the inverted condition and renamed for clarity.
    predicate in_BST(t: Tree, search_val: int)
    {
        match t
            case Null => false
            case Node(l, node_val, r) =>
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
            case Node(l_child, node_val, r_child) => 
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

    // TODO: DISALLOW DUPLICATES HERE BY ADDING ANOTHER CONDITION
    function isBST(t: Tree): bool
    {
        match t
            case Null => true
            case Node(l_child,v,r_child) => 
               isBST(l_child) && isBST(r_child) 
               && forall x: int :: 0 <= x < v && in_BST(l_child, x) ==> (x < v) // Valid tree structure & ordering property holds
               && forall x: int :: v < x && in_BST(r_child, x) ==> (x > v)
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
        case Node(curr_l, curr_v, curr_r) =>
            if (v < current_node.value) { // Insert as left child
                var tmp := add_recursive(current_node.left, v);
                ret := Node(tmp, curr_v, curr_r);
            }
            else { // Insert as right child
                var tmp := add_recursive(current_node.right, v);
                ret := Node(curr_l, curr_v, tmp);
            }
        case Null =>
            ret := Node(Null, v, Null);
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