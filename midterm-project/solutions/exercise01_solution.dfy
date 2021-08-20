//#title Midterm Project
//#desc Build a distributed lock server. Define your protocol in protocol.i;
//#desc write your safety spec and proof here.

// This challenge differs from LockServer in two ways. First, there is no
// central server that coordinates the activity. Second, the hosts can
// communicate only via asynchronous messages; a single state machine
// transition cannot simultaneously read or update the state of two hosts.
// 
// To guard against duplicate messages, the nodes associate a monotonically
// increasing epoch number with the lock. Initially, node 0 holds the lock and
// its epoch number is 1. A node that holds the lock can “grant” it to another
// node by sending them a “Grant” message which has an epoch number that is
// greater than the node's epoch number. A node that receives such a message
// will become the new holder and will set its epoch number to the message’v
// epoch number.  

// You'll first need to modify 'protocol.i.dfy' to define the protocol message
// format and the host behavior.
// Then come back here define the safety condition and prove that the
// distributed system made from that protocol maintains it.

include "distributed_system.s.dfy"

// the lock simulatneously.
predicate Safety(v:DistVars) {
//#exercise  false // Replace this placeholder with an appropriate safety condition: no two clients hold
//#start-elide
  && WFVars(v)
  && forall i, j :: v.hosts[i].holdsLock && v.hosts[j].holdsLock ==> i == j
//#end-elide
}

// TODO XXX should we give some signatures below as hints?
//#start-elide
predicate InFlight(v:DistVars, message:Message) {
  && WFVars(v)
  && message in v.network.messagesEverSent
  && message.epoch > v.hosts[message.dest].epoch
}

predicate UniqueMessageInFlight(v:DistVars) {
  forall m1, m2 :: InFlight(v, m1) && InFlight(v, m2) ==> m1 == m2
}

predicate InFlightPrecludesLockHeld(v:DistVars) {
  forall m :: InFlight(v, m) ==> (forall id :: !v.hosts[id].holdsLock)
}

predicate InFlightHasFreshestEpoch(v:DistVars) {
  forall m :: InFlight(v, m) ==> (forall id :: v.hosts[id].epoch < m.epoch)
}

predicate LockHolderPrecludesInFlight(v:DistVars)
  requires WFVars(v)
{
  forall id :: v.hosts[id].holdsLock ==> (forall m :: !InFlight(v, m))
}

predicate LockHolderHasFreshestEpoch(v:DistVars)
  requires WFVars(v)
{
  forall id :: v.hosts[id].holdsLock ==>
    (forall oid :: oid!=id ==> v.hosts[oid].epoch < v.hosts[id].epoch)
}

//#end-elide

predicate Inv(v:DistVars) {
//#exercise  true // Replace this placeholder with an invariant that's inductive and supports Safety.
//#start-elide
  && WFVars(v)

  // There are never two messages in flight.
  && UniqueMessageInFlight(v)

  // If a message is flight, no client holds the lock, and
  // the message has the freshest epoch number.
  && InFlightPrecludesLockHeld(v)
  && InFlightHasFreshestEpoch(v)

  // If a clent holds the lock, no message is in flight, and
  // the client has the freshest epoch number.
  && LockHolderPrecludesInFlight(v)
  && LockHolderHasFreshestEpoch(v)

  && Safety(v)
//#end-elide
}

lemma SafetyProof()
  ensures forall v :: DistInit(v) ==> Inv(v)
  ensures forall v, v' :: Inv(v) && DistNext(v, v') ==> Inv(v')
  ensures forall v :: Inv(v) ==> Safety(v)
{
//#start-elide
  forall v, v' | Inv(v) && DistNext(v, v') ensures Inv(v') {
    var id, a :| NextStep(v, v', id, a);
    if DoAccept(id, v.hosts[id], v'.hosts[id], a) {
      assert UniqueMessageInFlight(v);  // observe
      assert forall m | InFlight(v', m) :: InFlight(v, m);  // observe
      forall m ensures !InFlight(v', m) {
        assert InFlight(v, a.rcv.value);  // observe
        assert !InFlight(v', a.rcv.value);  // observe
      }
      assert Inv(v'); // observe
    } else {
      var recipient :| DoGrant(v.hosts[id], v'.hosts[id], a, recipient); // observe
      assert Inv(v'); // observe
    }
  }
//#end-elide
}
