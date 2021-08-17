//#title IsSeqSorted
//#desc Build an entire imperative loop method implementation with loop
//#desc invariants.

predicate IsSorted(intseq:seq<int>) {
    forall i:nat,j:nat | i<j<|intseq| :: intseq[i] <= intseq[j]
}

method IsSeqSorted(intSeq:seq<int>) returns (issorted:bool)
    ensures issorted <==> IsSorted(intSeq[..])
{
//#exercise    return true;
//#start-elide
    if(|intSeq| < 2) {
        return true;
    }
    var idx:=0;
    while(idx<|intSeq|-1) 
        invariant idx <= |intSeq|-1
        invariant forall i:nat,j:nat | i<j<idx+1 :: intSeq[i] <= intSeq[j]
    {
        if(intSeq[idx] > intSeq[idx+1]) {
           return false;
        }
        idx := idx+1;
    }
    return true;
//#end-elide
}

