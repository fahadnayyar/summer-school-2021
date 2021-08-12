//#title IsSorted
//#desc More specification practice.

predicate IsSorted(s:seq<int>)
{
  forall i :: 0 <= i < |s|-1 ==> s[i] <= s[i+1]
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

method merge(a:seq<int>, b:seq<int>) returns (output:seq<int>)
  requires IsSorted(a)
  requires IsSorted(b)
//#exercise  ensures IsSorted(output)
//#start-elide
  ensures SortSpec(a+b, output)
  //decreases |a|+|b|
//#end-elide
{
//#exercise  // Supply the body.
//#start-elide
  var ai := 0;
  var bi := 0;
  output := [];
  while ai < |a| || bi < |b|
    invariant 0 <= ai <= |a|
    invariant 0 <= bi <= |b|
    invariant 0 < |output| && ai < |a| ==> output[|output|-1] <= a[ai]
    invariant 0 < |output| && bi < |b| ==> output[|output|-1] <= b[bi]
    invariant forall i :: 0 <= i < |output|-1 ==> output[i] <= output[i+1]
    invariant multiset(output) == multiset(a[..ai]) + multiset(b[..bi])
    decreases |a|-ai + |b|-bi
  {
    ghost var outputo := output;
    ghost var ao := ai;
    ghost var bo := bi;
    if ai == |a| || (bi < |b| && a[ai] > b[bi]) {
      output := output + [b[bi]];
      bi := bi + 1;
      assert b[bo..bi] == [b[bo]];  // discovered by calc
    } else {
      output := output + [a[ai]];
      ai := ai + 1;
      assert a[ao..ai] == [a[ao]];  // discovered by calc
    }
    assert a[..ai] == a[..ao] + a[ao..ai];  // discovered by calc
    assert b[..bi] == b[..bo] + b[bo..bi];  // discovered by calc
//    calc {
//      multiset(a[..ai]) + multiset(b[..bi]);
//      multiset(a[..ao] + a[ao..ai]) + multiset(b[..bo] + b[bo..bi]);
//      multiset(a[..ao]) + multiset(a[ao..ai]) + multiset(b[..bo]) + multiset(b[bo..bi]);
//      multiset(a[..ao]) + multiset(b[..bo]) + multiset(a[ao..ai]) + multiset(b[bo..bi]);
//      multiset(outputo) + multiset(a[ao..ai]) + multiset(b[bo..bi]);
//      multiset(output);
//    }
  }
  assert a == a[..ai];  // derived by calc
  assert b == b[..bi];
//  calc {
//    multiset(output);
//    multiset(a[..ai]) + multiset(b[..bi]);
//    multiset(a) + multiset(b);
//    multiset(a + b);
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
