//#title Binary Tree Is Sorted
//#desc Prove an implementation meets its spec.
//#desc Practice with proof diagnosis.

// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each (internal) node has a value and at
// most two children, which are referred to as the left child and the right child.

//#exercisedatatype Tree = Tree // you should define your Tree datatype here
//#start-elide
datatype Tree = Nil | Node(value:int, left:Tree, right:Tree)
//#end-elide

// You will find the following function method useful. It is meant to express
// the given tree as a sequence.
//
// New syntax:  a function method is just like any other function, except it
// can be used in an "imperative" context (i.e., inside a method)

function method TreeAsSequence(tree:Tree) : seq<int>
{
//#exercise    [] // Replace me
//#start-elide
    if tree.Nil? then []
    else TreeAsSequence(tree.left) + [tree.value] + TreeAsSequence(tree.right)
//#end-elide
}

// Note: Don't use SequenceIsSorted in your definition of IsSortedTree.
predicate IsSortedTree(tree:Tree) {
//#exercise    true // Replace me
//#start-elide
    if (tree.Nil?)
    then true
    else
        && (forall j | 0 <= j < |TreeAsSequence(tree.left)| :: TreeAsSequence(tree.left)[j] <= tree.value)
        && (forall j | 0 <= j < |TreeAsSequence(tree.right)| :: tree.value <= TreeAsSequence(tree.right)[j])
        && IsSortedTree(tree.left)
        && IsSortedTree(tree.right)
//#end-elide
}

// You may find it useful to relate your recursive definition of IsSortedTree to
// a sequential representation of the tree structure

predicate SequenceIsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

lemma SortedTreeMeansSortedSequence(tree:Tree)
    requires IsSortedTree(tree)
    ensures SequenceIsSorted(TreeAsSequence(tree))
{
}

method CheckIfSortedTree(tree:Tree) returns (sorted:bool)
    ensures sorted <==> IsSortedTree(tree)
{
//#exercise    return false;
//#start-elide
    if (tree.Nil?) {
        return true;
    } else {
        var leftSorted := CheckIfSortedTree(tree.left);
        var rightSorted := CheckIfSortedTree(tree.right);
        if (!leftSorted || !rightSorted) {
            assert !IsSortedTree(tree);
            return false;
        } else {
            var leftSeq := TreeAsSequence(tree.left);
            var rightSeq := TreeAsSequence(tree.right);
            var isValueAfterLeft:bool := |leftSeq| == 0 || leftSeq[|leftSeq|-1] <= tree.value;
            var isValueBeforeRight:bool := |rightSeq| == 0 || tree.value <= rightSeq[0];
            if(!isValueAfterLeft) {
                return false;
            } else if (!isValueBeforeRight) {
                return false;
            } else {
                SortedTreeMeansSortedSequence(tree.left);
                SortedTreeMeansSortedSequence(tree.right);
                return true;
            }
        }
    }
//#end-elide
}
