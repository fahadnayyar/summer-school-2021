method merge_sort(input:seq<int>) returns (output:seq<int>)
  ensures IsSorted(output)
{
  if |input| <= 1 {
    output := input;
  } else {
    var pivotIndex := |input| / 2;
    var left := input[..pivotIndex];
    var right := input[pivotIndex..];
    if left!=[] {
      left := merge_sort(left);
    }
    if right!=[] {
      right := merge_sort(right);
    }
    output := merge(left, right);
  }
}
