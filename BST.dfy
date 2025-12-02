// CMPT 477
// Aarham Haider, Sumandeep Kaur, Nayoung Kim, Lucas Tangilag, Natalie Woods

// JAVA REFERENCE: https://github.com/dtfiedler/java-binary-tree/blob/master/src/BinaryTree.java

include "predicates/BSTPredicates.dfy"
include "types/Tree.dfy"
include "utils/Lemmas.dfy"
include "utils/Utils.dfy"
include "operations/BSTInsertDelete.dfy"
include "operations/BSTRotate.dfy"
include "operations/BSTSuccessorPredecessor.dfy"
include "operations/BSTTraversal.dfy"
module BST {
    import T = TreeModule
    import U = Utils
    import Pred = BSTPredicates
    import L = Lemmas
    import AddDelete = BSTInsertDelete
    import Rotate = BSTRotate
    import SuccessorPredecessor = BSTSuccessorPredecessor
    import Traversal = BSTTraversal

  class BST {
    var root: T.Tree

    constructor(r: T.Tree)
        ensures Pred.isBST(root)
    {
       root := r;
       new; 
       if (!Pred.isBST(r)) {
        root := T.Null; 
       }
    }

    method Insert(v: int)
        modifies this
        requires Pred.isBST(this.root)
        ensures Pred.isBST(this.root)
    {
        this.root := AddDelete.add_recursive(this.root, v);
    }

    method Delete(v: int)
        modifies this
        requires Pred.isBST(this.root)
        ensures this.root != T.Null || Pred.isBST(this.root)
    {
        if this.root != T.Null {
            this.root := AddDelete.delete_recursive(this.root, v);
        }
    }

    method LeftRotate(x: T.Tree) returns (ret: T.Tree)
        requires x != T.Null && x.right != T.Null
        requires Pred.isBST(x)                
        ensures ret != T.Null
        ensures T.tree_values(ret) == T.tree_values(x) 
    {
        ret := Rotate.left_rotate(x);
    }

    method RightRotate(y: T.Tree) returns (ret: T.Tree)
        requires y != T.Null && y.left != T.Null
        requires Pred.isBST(y)             
        ensures ret != T.Null
        ensures T.tree_values(ret) == T.tree_values(y)  
    {
        ret := Rotate.right_rotate(y);
    }

    method Successor(t: T.Tree) returns (s: int, hasSucc: bool)
        requires t != T.Null
        requires Pred.in_BST(this.root, t.value)
        requires Pred.isBST(this.root)
        ensures Pred.isBST(old(this.root))
        ensures Pred.in_BST(this.root, t.value)
        ensures hasSucc ==> (t.right != T.Null ==> s == T.min_value_in_tree(t.right))
    {
        s, hasSucc := SuccessorPredecessor.successor(t, this.root);
    }

    method Predecessor(t: T.Tree) returns (pval: int, hasPred: bool)
        requires t != T.Null
        requires Pred.in_BST(this.root, t.value)
        requires Pred.isBST(this.root)
        ensures hasPred ==> (t.left != T.Null ==> pval == T.max_value_in_tree(t.left))
    {
        pval, hasPred := SuccessorPredecessor.predecessor(t, this.root);
    }

    method InorderTraversal(t: T.Tree) returns (result: seq<int>)
        requires Pred.isBST_for_traversal(t) // valid BST
        ensures forall i :: 0 <= i < |result| ==> result[i] in T.tree_values(t)
        ensures |result| == |T.tree_values(t)|
        ensures Pred.is_sorted(result)
        ensures result == U.inorder_traversal_seq(t)
        decreases t
    {
        result := Traversal.inorder_traversal(t);
    }

    method PreorderTraversal(t: T.Tree) returns (result: seq<int>)
        requires Pred.isBST_for_traversal(t)
        ensures forall i :: 0 <= i < |result| ==> result[i] in T.tree_values(t)
        ensures |result| == |T.tree_values(t)|
        decreases t
    {
        result := Traversal.preorder_traversal(t);
    }

    method PostorderTraversal(t: T.Tree) returns (result: seq<int>)
        requires Pred.isBST_for_traversal(t)
        ensures forall i :: 0 <= i < |result| ==> result[i] in T.tree_values(t)
        ensures |result| == |T.tree_values(t)|
        decreases t
    {
        result := Traversal.postorder_traversal(t);
    }

  }
}