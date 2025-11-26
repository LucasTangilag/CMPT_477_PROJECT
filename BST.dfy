// CMPT 477
// Aarham Haider, Sumandeep Kaur, Nayoung Kim, Lucas Tangilag, Natalie Woods

// JAVA REFERENCE: https://github.com/dtfiedler/java-binary-tree/blob/master/src/BinaryTree.java

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

    // Helper: find maximum element of t
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

    //Helper that gets all values in a tree as a set
    function tree_values(t: Tree): multiset<int>
    {
        match t
        case Null => multiset{}
        case Node(l, v, r, _) =>
            multiset{v} + tree_values(l) + tree_values(r)
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
        ensures ret ==> in_BST(t, search_val)
        decreases t
    {
        match t
            case Node(l_child, node_val, r_child, _) => 
                if (node_val == search_val) {
                    ret := true;
                } else if (search_val < node_val) { // less-than case
                    if (l_child == Null) {
                        ret := false;
                    } else {
                        ret := value_in_tree(l_child, search_val);
                    }
                } else { // greater-than case
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

    predicate isBST(t: Tree)
    {
        match t
            case Null => true
            case Node(l_child,v,r_child, _) => 
                isBST(l_child) 
                && isBST(r_child) 
                && if (t.parent != Null) then (t == t.parent.left ==> t.value < t.parent.value) && (t == t.parent.right ==> t.value > t.parent.value) else true
                && (l_child != Null ==> all_less_than(l_child, v))
                && (r_child != Null ==> all_greater_than(r_child, v))
    }


    // Appends a new value, v, as a descendent of current_node
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
    method insert(v: int)
        modifies this
        requires isBST(this.root)
        ensures isBST(this.root)

    {
        this.root := add_recursive(this.root, v);
    }

    /* DELETE */
    function SetParent(t: Tree, p: Tree): Tree
    {
        match t
        case Null => Null
        case Node(l, v, r, _) => Node(SetParent(l, t), v, SetParent(r, t), p)
    }

    // Helper to find inorder successor
    method find_min(t: Tree) returns (min_val: int)
        requires t != Null
        ensures min_val == min_value_in_tree(t)
        decreases t
    {
        match t
        case Node(l, v, r, _) =>
            if l == Null {
                min_val := v;
            } else {
                min_val := find_min(l);
            }
    }

    // Verified delete_recursive; returns copy of tree without v
    method delete_recursive(current_node: Tree, v: int) returns (ret: Tree)
        requires isBST(current_node)
        ensures ret !=Null || isBST(ret)
        decreases current_node
    {
        if current_node == Null {
            ret := Null;
            return;
        }

        match current_node
        case Node(curr_l, curr_v, curr_r, curr_parent) =>
            if v < curr_v {
                var new_left := delete_recursive(curr_l, v);
                ret := Node(new_left, curr_v, curr_r, curr_parent);
            } else if v > curr_v {
                var new_right := delete_recursive(curr_r, v);
                ret := Node(curr_l, curr_v, new_right, curr_parent);
            } else {
                // Node to delete
                if curr_l == Null {
                    ret := SetParent(curr_r, curr_parent);
                } else if curr_r == Null {
                    ret := SetParent(curr_l, curr_parent);
                } else {
                    // Node with two children: find successor
                    var successor_val := find_min(curr_r);
                    var new_right := delete_recursive(curr_r, successor_val);
                    ret := Node(curr_l, successor_val, SetParent(new_right, current_node), curr_parent);
                }
            }
    }

    // Delete method modifying the BST
    method delete(v: int)
        modifies this
        requires isBST(this.root)
        ensures this.root != Null || isBST(this.root)
    {
        if this.root != Null {
            this.root := delete_recursive(this.root, v);
        }
    }

    // ROTATIONS
    // Right rotate y around its left child x
    //          y                         x
    //        /   \                     /   \
    //       x     C       ->           A     y
    //     /   \                           /   \
    //    A     B                         B     C
    
    method right_rotate(y: Tree) returns (ret: Tree)
        requires y != Null && y.left != Null
        requires isBST(y)             
        ensures ret != Null
        ensures tree_values(ret) == tree_values(y)  
    {
        match y
        case Node(x, y_val, C, y_parent) =>
            match x
            case Node(A, x_val, B, x_parent) =>
                //build new y node with B and C as its children
                var new_y := Node(B, y_val, C, Null);
                //build new root node with A and new_y as its children
                ret := Node(A, x_val, new_y, y_parent);
    }

    // Left rotate x around its right child y
    //         x                           y
    //       /   \                       /   \
    //      A     y        ->           x     C
    //          /   \                 /   \
    //         B     C               A     B

    method left_rotate(x: Tree) returns (ret: Tree)
        requires x != Null && x.right != Null
        requires isBST(x)                
        ensures ret != Null
        ensures tree_values(ret) == tree_values(x) 
    {
        match x
        case Node(A, x_val, y, x_parent) =>
            match y
            case Node(B, y_val, C, y_parent) =>
                //build new x node with A and B as its children
                var new_x := Node(A, x_val, B, Null);
                //build new root node with new_x and C as its children
                ret := Node(new_x, y_val, C, x_parent);
    }

    // Returns the height of the tree (Null has height 0)
    function height(t: Tree): int
        ensures t == Null ==> height(t) == 0
        ensures t != Null ==> height(t) > 0
        decreases t
    {
        match t
        case Null => 0
        case Node(l, _, r, _) => 1 + if height(l) > height(r) then height(l) else height(r)
    }

    method successor(t: Tree) returns (s: int, hasSucc: bool)
        requires t != Null
        requires in_BST(this.root, t.value)
        requires isBST(this.root)
        ensures isBST(old(this.root))
        ensures in_BST(this.root, t.value)
        ensures hasSucc ==> (t.right != Null ==> s == min_value_in_tree(t.right))
    {
        match t
        case Node(_, v, r, p) =>

            if r != Null {
                s := min_value_in_tree(r);
                hasSucc := true;
                return;
            }

            var curr := t;
            var par := p;

            while par != Null && curr == match par case Node(_,_,r2,_) => r2
                decreases par
            {
                curr := par;
                match par
                case Node(_,_,_,pp) => par := pp;
            }

            if par == Null {
                hasSucc := false;
                s := v; 
            } else {
                match par
                case Node(_, pv, _, _) =>
                    s := pv;
                    hasSucc := true;
            }
    }

    method predecessor(t: Tree) returns (pval: int, hasPred: bool)
        requires t != Null
        requires in_BST(this.root, t.value)
        requires isBST(this.root)
        ensures hasPred ==> (t.left != Null ==> pval == max_value_in_tree(t.left))
    {
        match t
        case Node(l, v, r, parent) =>

            // CASE 1: predecessor is in left subtree
            if l != Null {
                pval := max_value_in_tree(l);
                hasPred := true;
                return;
            }

            // CASE 2: walk up until we find a parent where we came from the right
            var curr := t;
            var par := parent;

            while par != Null && curr == match par case Node(l2, _, _, _) => l2
                decreases par
            {
                curr := par;
                match par
                case Node(_, _, _, pp) => par := pp;
            }

            if par == Null {
                // no predecessor exists
                hasPred := false;
                pval := v;  
            } else {
                match par
                case Node(_, pv, _, _) =>
                    pval := pv;
                    hasPred := true;
            }
    }

    /* Traversal */

    // Check the validity of BST
    predicate isBST_for_traversal(t: Tree)
    {
        match t
            case Null => true
            case Node(l_child, v, r_child, _) =>
                isBST_for_traversal(l_child)
                && isBST_for_traversal(r_child)
                && all_less_than(l_child, v)
                && all_greater_than(r_child, v)
    }

    // Check if input sequence is sorted in ascending order
    predicate is_sorted(s: seq<int>)
    {
        forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
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

    // Mathematical definition of inorder traversal (for reasoning)
    // : produce a sequence in inorder traversal order
    function inorder_traversal_seq(t: Tree): seq<int>
        requires isBST_for_traversal(t)
        decreases t
    {
        match t
        case Null => []
        case Node(l, v, r, _) =>
            inorder_traversal_seq(l) + [v] + inorder_traversal_seq(r)
    }

    // Helps Dafny verify inorder_is_sorted
    // : prove that if all tree values are less than bound, then so is the inorder sequence (connect tree properties to sequence properties)
    lemma all_less_than_to_seq(t: Tree, bound: int)
        requires isBST_for_traversal(t)
        requires all_less_than(t, bound)
        ensures seq_all_less_than(inorder_traversal_seq(t), bound)
        decreases t
    {
        match t
        case Null => {}
        case Node(l, v, r, _) =>
            all_less_than_to_seq(l, bound);
            all_less_than_to_seq(r, bound);
    }

    // Helps Dafny verify inorder_is_sorted
    // : prove that if all tree values are greater than bound, then so is the inorder sequence (connect tree properties to sequence properties)
    lemma all_greater_than_to_seq(t: Tree, bound: int)
        requires isBST_for_traversal(t)
        requires all_greater_than(t, bound)
        ensures seq_all_greater_than(inorder_traversal_seq(t), bound)
        decreases t
    {
        match t
        case Null => {}
        case Node(l, v, r, _) =>
            all_greater_than_to_seq(l, bound);
            all_greater_than_to_seq(r, bound);

    }

    // Helps Dafny verify inorder_traversal
    // : prove that inorder traversal gives sorted output for valid BST
    lemma inorder_is_sorted(t: Tree)
        requires isBST_for_traversal(t)
        ensures is_sorted(inorder_traversal_seq(t))
        decreases t
    {
        match t
        case Null => {}
        case Node(l, v, r, _) =>
            inorder_is_sorted(l);
            inorder_is_sorted(r);

            assert all_less_than(l, v);
            assert all_greater_than(r, v);

            all_less_than_to_seq(l, v);
            all_greater_than_to_seq(r, v);
    }

    // Implementation of inorder traversal
    // : left subtree -> current node -> right subtree
    method inorder_traversal(t: Tree) returns (result: seq<int>)
        requires isBST_for_traversal(t) // valid BST
        // 1. all values in result exist in tree
        ensures forall i :: 0 <= i < |result| ==> result[i] in tree_values(t)
        // 2. result size equals tree size (no missing or extra tree values)
        ensures |result| == |tree_values(t)|
        // 3. inorder traversal's result is sorted
        ensures is_sorted(result)
        // 4. inorder traversal's result matches the mathematical function
        ensures result == inorder_traversal_seq(t)
        decreases t
    {
        match t
        case Null =>
            result := [];
        case Node(l, v, r, _) => 
            var left_result := inorder_traversal(l);
            var right_result := inorder_traversal(r);
            result := left_result + [v] + right_result;

            inorder_is_sorted(t);
            assert result == inorder_traversal_seq(t);
    }

    // Implementation of preorder traversal
    // : root node -> left subtree -> right subtree
    method preorder_traversal(t: Tree) returns (result: seq<int>)
        requires isBST_for_traversal(t)
        // 1. all values in result exists in tree
        ensures forall i :: 0 <= i < |result| ==> result[i] in tree_values(t)
        // 2. result size equals tree size (no missing or extra tree values)
        ensures |result| == |tree_values(t)|
        decreases t
    {
        match t
        case Null =>
            result := [];
        case Node(l, v, r, _) =>
            var left_result := preorder_traversal(l);
            var right_result := preorder_traversal(r);
            result := [v] + left_result + right_result;
    }

    // Implementation of postorder traversal
    // : left subtree -> right subtree -> root node
    method postorder_traversal(t: Tree) returns (result: seq<int>)
        requires isBST_for_traversal(t)
        // 1. all values in result exist in tree
        ensures forall i :: 0 <= i < |result| ==> result[i] in tree_values(t)
        // 2. result size equals tree size (no missing or extra tree values)
        ensures |result| == |tree_values(t)|
        decreases t
    {
        match t
        case Null =>
            result := [];
        case Node(l, v, r, _) =>
            var left_result := postorder_traversal(l);
            var right_result := postorder_traversal(r);
            result := left_result + right_result + [v];
    }
}