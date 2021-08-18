method merge(seqa:seq<int>, seqb:seq<int>) returns (output:seq<int>)
  requires IsSorted(seqa)
  requires IsSorted(seqb)
  ensures IsSorted(output)
{
  var aidx := 0;
  var bidx := 0;
  output := [];
  while aidx < |seqa| || bidx < |seqb|
    decreases |seqa|-aidx + |seqb|-bidx
  {
    if aidx == |seqa| || (bidx < |seqb| && seqa[aidx] > seqb[bidx]) {
      output := output + [seqb[bidx]];
      bidx := bidx + 1;
    } else {
      output := output + [seqa[aidx]];
      aidx := aidx + 1;
    }
  } 
}
