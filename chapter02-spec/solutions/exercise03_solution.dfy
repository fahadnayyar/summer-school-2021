//#title Merge Sort
//#desc More specification practice.

// Implement a merge sort that guarantees the result is sorted.
// merge() sohuld merge its two sorted inputs into a sorted output.
// merge_sort picks a pivot, recursively merge_sort()s the subsequences,
// and then uses merge() to put them back together. We've provided
// signatures for merge and merge_sort to get you started.

predicate IsSorted(seqint:seq<int>)
{
  forall idx :: 0 <= idx < |seqint|-1 ==> seqint[idx] <= seqint[idx+1]
}

//#start-elide
predicate SortSpec(input:seq<int>, output:seq<int>)
{
  && IsSorted(output)
  && multiset(output) == multiset(input)
}

//#end-elide
method merge_sort(input:seq<int>) returns (output:seq<int>)
//#exercise  ensures IsSorted(output)
//#start-elide
  ensures SortSpec(input, output)
//#end-elide
{
//#exercise  // Supply the body.
//#start-elide
  if |input| <= 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    var leftSorted := left;
    leftSorted := merge_sort(left);
    var rightSorted := right;
    rightSorted := merge_sort(right);
    output := merge(leftSorted, rightSorted);
    assert left + right == input; // derived via calc
//    calc {
//      multiset(output);
//      multiset(leftSorted + rightSorted);
//      multiset(leftSorted) + multiset(rightSorted);
//      multiset(left) + multiset(right);
//      multiset(left + right);
//        { assert left + right == input; }
//      multiset(input);
//    }
  }
//#end-elide
}

method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
  requires IsSorted(seqa)
  requires IsSorted(seqb)
//#exercise  ensures IsSorted(output)
//#start-elide
  ensures SortSpec(seqa+seqb, output)
  //decreases |seqa|+|seqb|
//#end-elide
{
//#exercise  // Supply the body.
//#start-elide
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |seqa| || bi < |seqb|
    invariant 0 <= ai <= |seqa|
    invariant 0 <= bi <= |seqb|
    invariant 0 < |output| && ai < |seqa| ==> output[|output|-1] <= seqa[ai]
    invariant 0 < |output| && bi < |seqb| ==> output[|output|-1] <= seqb[bi]
    invariant forall i :: 0 <= i < |output|-1 ==> output[i] <= output[i+1]
    invariant multiset(output) == multiset(seqa[..ai]) + multiset(seqb[..bi])
    decreases |seqa|-ai + |seqb|-bi
  {
    ghost var outputo := output;
    ghost var ao := ai;
    ghost var bo := bi;
    if ai == |seqa| || (bi < |seqb| && seqa[ai] > seqb[bi]) {
      output := output + [seqb[bi]];
      bi := bi + 1;
      assert seqb[bo..bi] == [seqb[bo]];  // discovered by calc
    } else {
      output := output + [seqa[ai]];
      ai := ai + 1;
      assert seqa[ao..ai] == [seqa[ao]];  // discovered by calc
    }
    assert seqa[..ai] == seqa[..ao] + seqa[ao..ai];  // discovered by calc
    assert seqb[..bi] == seqb[..bo] + seqb[bo..bi];  // discovered by calc
//    calc {
//      multiset(seqa[..ai]) + multiset(seqb[..bi]);
//      multiset(seqa[..ao] + seqa[ao..ai]) + multiset(seqb[..bo] + seqb[bo..bi]);
//      multiset(seqa[..ao]) + multiset(seqa[ao..ai]) + multiset(seqb[..bo]) + multiset(seqb[bo..bi]);
//      multiset(seqa[..ao]) + multiset(seqb[..bo]) + multiset(seqa[ao..ai]) + multiset(seqb[bo..bi]);
//      multiset(outputo) + multiset(seqa[ao..ai]) + multiset(seqb[bo..bi]);
//      multiset(output);
//    }
  }
  assert seqa == seqa[..ai];  // derived by calc
  assert seqb == seqb[..bi];
//  calc {
//    multiset(output);
//    multiset(seqa[..ai]) + multiset(seqb[..bi]);
//    multiset(seqa) + multiset(seqb);
//    multiset(seqa + seqb);
//  }
//#end-elide
}
//#start-elide

method fast_sort(input:seq<int>) returns (output:seq<int>)
//  ensures SortSpec(input, output)
{
  output := [1, 2, 3];
}
//#end-elide
