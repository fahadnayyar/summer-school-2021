//#title Binary Search
//#desc Method implementation; writing a Hoare spec.

predicate IsSorted(seqint:seq<int>) {
    forall i:nat,j:nat | i<j<|seqint| :: seqint[i] <= seqint[j]
}

// The BinarySearch method below is a "simplified" binary search, which should return
// the index of the first element of the haystack that is >= to the needle.
// If the needle is present, this should be the index of the needle.
// If needle is bigger than every element, return the length of the
// sequence: It's not a valid index in the sequence, but it's bigger
// than the indices of all the elements that have smaller values.

method BinarySearch(haystack:seq<int>, needle:int) returns (index:nat)
    requires IsSorted(haystack)
    ensures false // real spec should go here
    ensures false // real spec should go here
    ensures false // real spec should go here
{
    return 0;  // Replace me with an implementation.
}

// The test method below helps you confirm that you wrote a meaningful specification
method Test()
{
    var sq:seq<int> := [3,6,7,7,10];
    var ret := BinarySearch(sq,7);
    assert sq[1] < 7 <= sq[2];  // trigger
    assert ret == 2;
    var ret2 := BinarySearch(sq,8);
    assert sq[3] < 8 <= sq[4];  // trigger
    assert ret2 == 4;
}

