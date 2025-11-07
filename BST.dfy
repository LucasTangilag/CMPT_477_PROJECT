// CMPT 477
// Aarham Haider, Sumandeep Kaur, Nayoung Kim, Lucas Tangilag, Natalie Woods

// JAVA REFERENCE: https://github.com/dtfiedler/java-binary-tree/blob/master/src/BinaryTree.java

/*
    [Lucas]:

    TODO: DOUBLE CHECK LUCAS' IMPLEMENTATIONS FOR INSERT AND FIND, ENSURE VALIDITY HOLDS
    TODO: IMPLEMENT & VERIFY DELETE FUNCTION
    TODO: IMPLEMENT & VERIFY TREE TRAVERSALS
*/

datatype Tree = Null | Node(left: Tree, value: int, right: Tree)

class BST{
    var root: Tree

    constructor(r: Tree) 
        ensures isBST(r) ==> isBST(root)
    {
        root := r;
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

    // [Lucas]: Fixed to verify fully. Strengthened ensures to iff, removed unreachable Null case, removed assumes, renamed for clarity.
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

    function isBST(t: Tree): bool
    {
        match t
            case Null => true
            case Node(l_child,_,r_child) => 
               isBST(l_child) && isBST(r_child) && (l_child != Null ==> max_value_in_tree(l_child) < t.value) && (r_child != Null ==> min_value_in_tree(r_child) > t.value)
    }

    // [Lucas]:
    // Appends a new value, v, as a descendent of current_node
    // TODO : ENSURE PROPER ORDERING AS POST CONDITION
    // TODO : ADD ANY OTHER APPROPRIATE VERIFICATION CONDITIONS 
    method add_recursive(current_node: Tree, v: int) returns (ret: Tree)
        requires isBST(current_node)
        ensures isBST(ret)
    {
        if (current_node == Null) {
            ret := Node(Null, v, Null);
        } else {
            if (v < current_node.value) { // Insert as left child
                ret := add_recursive(current_node.left, v);
            }
            else { // Insert as right child
                ret := add_recursive(current_node.right, v);
            }
        }
    }

    // [Lucas]:
    // So far, we just assume that we have a valid structure, and then that insertion doesn't break our structure
    // TODO: FIND A WAY TO VERIFY THAT, FROM THE VERY BEGINNING, THE BST PROPERTIES HOLD
    method insert(v: int)
        requires isBST(this.root)
        ensures isBST(this.root)
        modifies this
    {
        this.root := add_recursive(this.root, v);
    }
}