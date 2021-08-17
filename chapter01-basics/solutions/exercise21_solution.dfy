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
//#exercise    ensures false // real spec should go here
//#exercise    ensures false // real spec should go here
//#exercise    ensures false // real spec should go here
//#start-elide
    ensures index <= |haystack|
    ensures forall i:nat | i<index :: haystack[i] < needle
    ensures forall i:nat | index<=i<|haystack| :: needle <= haystack[i]
//#end-elide
{
//#exercise    return 0;  // Replace me with an implementation.
//#start-elide
    var low:nat := 0;
    var high:nat := |haystack|;
     
    while(low < high)
        invariant low <= high <= |haystack| 
        invariant forall i:nat | i < low :: haystack[i] < needle
        invariant forall i:nat | high <= i < |haystack| :: needle <= haystack[i]
    {
        var mid := (low+high)/2;
        if(haystack[mid] < needle) {
            low := mid+1;
        } else {
            high := mid;
        }
        
    }
    return low; 
//#end-elide
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

