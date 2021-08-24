//#title Binary Tree Is Sorted
//#desc Prove an implementation meets its spec.
//#desc Practice with proof diagnosis.

include "../../library/Library.dfy"
import opened Library

// Define a Binary Tree and write a method to check if it is sorted

// A binary tree is a tree data structure in which each (internal) node has a value and at
// most two children, which are referred to as the left child and the right child.

datatype Tree = Tree // you should define your Tree datatype here

// You will find the following function method useful. It is meant to express
// the given tree as a sequence.
//
// New syntax:  a function method is just like any other function, except it
// can be used in an "imperative" context (i.e., inside a method)

function method TreeAsSequence(tree:Tree) : seq<int>
{
    [] // Replace me
}

// If this predicate is true about sorted sequences, then everything
// in seq1 is <= everything in seq2.
predicate SequencesOrderedAtInterface(seq1:seq<int>, seq2:seq<int>)
{
  if |seq1|==0 || |seq2|==0
  then true
  else Last(seq1) <= seq2[0]
}

// Note: Don't use SequenceIsSorted in your definition of IsSortedTree.
predicate IsSortedTree(tree:Tree) {
    true // Replace me
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

