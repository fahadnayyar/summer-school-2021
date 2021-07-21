// Each node's identifier (address)
datatype Constants = Constants(ids: seq<nat>) {
  predicate ValidIdx(i: nat) {
    0<=i<|ids|
  }

  predicate UniqueIds() {
    (forall i:nat, j:nat | ValidIdx(i) && ValidIdx(j) && ids[i]==ids[j] :: i == j)
  }

  predicate WF() {
    && 0 < |ids|
  }
}

// The highest other identifier this node has heard about.
datatype Variables = Variables(highest_heard: seq<int>) {
  predicate WF(k: Constants)
    requires k.WF()
  {
    && |highest_heard| == |k.ids|
  }
}

predicate Init(k: Constants, v: Variables)
{
  && k.WF()
  && v.WF(k)
    // Everyone begins having heard about nobody, not even themselves.
  && (forall i:nat | k.ValidIdx(i) :: v.highest_heard[i] == -1)
}

function max(a: int, b: int) : int {
  if a > b then a else b
}

function NextIdx(k: Constants, idx: nat) : nat
  requires k.WF()
  requires k.ValidIdx(idx)
{
  (idx + 1) % |k.ids|
}

predicate Transmission(k: Constants, v: Variables, v': Variables, src: nat)
{
  && k.WF()
  && v.WF(k)
  && v'.WF(k)
  && k.ValidIdx(src)

  // Neighbor address in ring.
  && var dst := NextIdx(k, src);

  // src sends the max of its highest_heard value and its own id.
  && var message := max(v.highest_heard[src], k.ids[src]);

  // dst only overwrites its highest_heard if the message is higher.
  && var dst_new_max := max(v.highest_heard[dst], message);
  // XXX Manos: How could this have been a bug!? How could a src, having sent message X, ever send message Y < X!?

  && v' == v.(highest_heard := v.highest_heard[dst := dst_new_max])
}

datatype Step = TransmissionStep(src: nat)

predicate NextStep(k: Constants, v: Variables, v': Variables, step: Step)
{
  match step {
    case TransmissionStep(src) => Transmission(k, v, v', src)
  }
}

predicate Next(k: Constants, v: Variables, v': Variables)
{
  exists step :: NextStep(k, v, v', step)
}

//////////////////////////////////////////////////////////////////////////////
// Spec (proof goal)
//////////////////////////////////////////////////////////////////////////////

predicate IsLeader(k: Constants, v: Variables, i: nat)
  requires k.WF()
  requires v.WF(k)
{
  && k.ValidIdx(i)
  && v.highest_heard[i] == k.ids[i]
}

predicate Safety(k: Constants, v: Variables)
  requires k.WF()
  requires v.WF(k)
{
  forall i, j | IsLeader(k, v, i) && IsLeader(k, v, j) :: i == j
}

//////////////////////////////////////////////////////////////////////////////
// Proof
//////////////////////////////////////////////////////////////////////////////

predicate Between(k: Constants, startExclusive: nat, i: nat, endExclusive: nat)
{
  if startExclusive < endExclusive
  then
    startExclusive < i < endExclusive
  else
    startExclusive < i || i < endExclusive
}

predicate IsChord(k: Constants, v: Variables, start: nat, end: nat)
{
  && k.WF()
  && v.WF(k)
  && k.ValidIdx(start)
  && k.ValidIdx(end)
  && k.ids[start] == v.highest_heard[end]
}
predicate HeardOnChordDominatesID(k: Constants, v: Variables, start: nat, end: nat)
{
  IsChord(k, v, start, end)
  ==> (forall i:nat | k.ValidIdx(i) && Between(k, start, i, end) :: v.highest_heard[i] > k.ids[i])
}

predicate HeardDominatesInv(k: Constants, v: Variables)
{
  && (forall start, end | k.ValidIdx(start) && k.ValidIdx(end) :: HeardOnChordDominatesID(k, v, start, end))
}

predicate Inv(k: Constants, v: Variables)
{
  && k.WF()
  && v.WF(k)
  && Safety(k, v)
  && HeardDominatesInv(k, v)
}

lemma Boink()
{
  var k := Constants([3, 3]);
  var v0 := Variables([-1, -1]);
  var v1 := Variables([-1, 3]);
  var v2 := Variables([3, 3]);
  assert Init(k, v0);
  assert Transmission(k, v0, v1, 0);
  assert Transmission(k, v1, v2, 1);
  assert IsLeader(k, v2, 0);
  assert IsLeader(k, v2, 1);
  assert !Safety(k, v2);
}

lemma InitImpliesInv(k: Constants, v: Variables)
  requires Init(k, v)
  ensures Inv(k, v)
{
}
  
lemma NextPreservesInv(k: Constants, v: Variables, v': Variables)
  requires Inv(k, v)
  requires Next(k, v, v')
  ensures Inv(k, v')
{
  var step :| NextStep(k, v, v', step);
  assert Transmission(k, v, v', step.src);
  forall start:nat, end:nat | k.ValidIdx(start) && k.ValidIdx(end) ensures HeardOnChordDominatesID(k, v', start, end)
  {
    if (
      && k.WF()
      && v'.WF(k)
      && k.ValidIdx(start)
      && k.ValidIdx(end)
      && k.ids[start] == v'.highest_heard[end]
    ) {
      forall i:nat | k.ValidIdx(i) && Between(k, start, i, end)
        ensures v'.highest_heard[i] > k.ids[i]
      {
        var src := step.src;
        var dst := NextIdx(k, src);
        if i==end {
          assert v'.highest_heard[i] > k.ids[i];
        } else if i==start {
          assert v'.highest_heard[i] > k.ids[i];
        } else if dst == end {
          // old chord changed
          assert v'.highest_heard[i] > k.ids[i];
        } else if dst == i {
          // start < i, dst < end, so transmission didn't change anything.
          assert v.highest_heard[end] == v'.highest_heard[end];
          assert k.ids[start] == v.highest_heard[end];
          assert v.highest_heard[i] > k.ids[i];
          assert v'.highest_heard[i] == v'.highest_heard[i];
          assert v'.highest_heard[src] == v'.highest_heard[src];
          var message := max(v.highest_heard[src], k.ids[src]);
          var dst_new_max := max(v.highest_heard[dst], message);
          assert v'.highest_heard[i] == dst_new_max;
          assert dst_new_max >= message;
          assert message >= k.ids[src];
          if (start == src) {
            assert v'.highest_heard[i] > k.ids[i];
          } else {
            if !Between(k, start, src, end) {
              assert Between(k, src, start, end);
              assert false;
            }
            assert Between(k, start, src, end);
            assert HeardOnChordDominatesID(k, v, start, end);
            assert IsChord(k, v, start, end);
            assert k.ids[start] == v.highest_heard[end];
            assert k.ids[src] > k.ids[i];
            assert v'.highest_heard[i] > k.ids[i];
          }
        } else {
          // new chord shows up?
          assert v'.highest_heard[i] > k.ids[i];
        }
      }
    }
  }
}

lemma InvImpliesSafety(k: Constants, v: Variables)
  requires Inv(k, v)
  ensures Safety(k, v)
{
}