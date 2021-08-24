//#title Midterm Project
//#desc Build a distributed lock server. Define how a host implements your
//#desc protocol in host.i; write your safety spec and proof here.

// This challenge differs from LockServer (from chapters 03 and 04) in two
// ways. First, there is no central server that coordinates the activity.
// Second, the hosts can communicate only via asynchronous messages; a single
// state machine transition cannot simultaneously read or update the state of
// two hosts.
// 
// To guard against duplicate messages, the nodes associate a monotonically
// increasing epoch number with the lock. Initially, node 0 holds the lock and
// its epoch number is 1. A node that holds the lock can “grant” it to another
// node by sending them a “Grant” message which has an epoch number that is
// greater than the node's epoch number. A node that receives such a message
// will become the new holder and will set its epoch number to the message’s
// epoch number.  

// You'll first need to modify 'host.i.dfy' to define the protocol message
// format and the host behavior.
// Then come back here define the safety condition and prove that the
// distributed system made from that protocol maintains it.

include "distributed_system.s.dfy"

module SafetySpec {
  import opened HostIdentifiers
  import DistributedSystem

  // No two hosts think they hold the lock simulatneously.
  predicate Safety(c:DistributedSystem.Constants, v:DistributedSystem.Variables) {
//#exercise    false // Replace this placeholder with an appropriate safety condition: no two clients hold
//#start-elide
    && v.WF(c)
    && (forall i, j
        | ValidHostId(i) && ValidHostId(j) && v.hosts[i].holdsLock && v.hosts[j].holdsLock
        :: i == j
      )
//#end-elide
  }
}

module Proof {
  import opened HostIdentifiers
  import Host
  import opened DistributedSystem
  import opened SafetySpec

  // Here's a predicate that will be very useful in constructing inviariant conjuncts.
  predicate InFlight(c:Constants, v:Variables, message:Host.Message) {
    && v.WF(c)
    && message in v.network.sentMsgs
//#exercise    && false // ...and then add a check that the message's epoch is still valid.
//#start-elide
    && ValidHostId(message.dest)
    && message.epoch > v.hosts[message.dest].epoch
//#end-elide
  }

//#start-elide
  predicate UniqueMessageInFlight(c: Constants, v:Variables) {
    forall m1, m2 | InFlight(c, v, m1) && InFlight(c, v, m2) :: m1 == m2
  }

  predicate InFlightPrecludesLockHeld(c: Constants, v:Variables) {
    forall m | InFlight(c, v, m) :: (forall id | ValidHostId(id) :: !v.hosts[id].holdsLock)
  }

  // We wrote this in a fit of symmetry, but it's equivalent to InFlightPrecludesLockHeld.
  // Once we figured that out, we wrote a lemma to convince myself, then deleted this conjunct
  // from Inv.
  predicate Unused_LockHolderPrecludesInFlight(c: Constants, v:Variables)
    requires v.WF(c)
  {
    forall id | ValidHostId(id) && v.hosts[id].holdsLock
      :: (forall m :: !InFlight(c, v, m))
  }

  predicate LockHolderHasFreshestEpoch(c: Constants, v:Variables)
    requires v.WF(c)
  {
    forall id | ValidHostId(id) && v.hosts[id].holdsLock
      :: (forall oid | ValidHostId(oid) && oid!=id :: v.hosts[oid].epoch < v.hosts[id].epoch)
  }

  predicate InFlightHasFreshestEpoch(c: Constants, v:Variables) {
    forall m | InFlight(c, v, m) :: (forall id | ValidHostId(id) :: v.hosts[id].epoch < m.epoch)
  }

//#end-elide

  predicate Inv(c: Constants, v:Variables) {
//#exercise    true // Replace this placeholder with an invariant that's inductive and supports Safety.
//#start-elide
    && v.WF(c)

    // There are never two messages in flight.
    && UniqueMessageInFlight(c, v)

    // If a message is flight, no client holds the lock, and vice versa
    && InFlightPrecludesLockHeld(c, v)

    // Whoever holds the lock (host or in-flight message) has the freshest epoch number.
    && LockHolderHasFreshestEpoch(c, v)
    && InFlightHasFreshestEpoch(c, v)

    && Safety(c, v)
//#end-elide
  }

  lemma SafetyProof(c: Constants, v:Variables, v':Variables)
    ensures Init(c, v) ==> Inv(c, v)
    ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
    ensures Inv(c, v) ==> Safety(c, v)
  {
    // Develop any necessary proof here.
//#start-elide
    forall v, v' | Inv(c, v) && Next(c, v, v') ensures Inv(c, v') {
      var step :| NextStep(c, v, v', step);
      if Host.DoAccept(c.hosts[step.id], v.hosts[step.id], v'.hosts[step.id], step.msgOps) {
        assert UniqueMessageInFlight(c, v);  // observe
        assert forall m | InFlight(c, v', m) :: InFlight(c, v, m);  // observe
        forall m ensures !InFlight(c, v', m) {
          assert InFlight(c, v, step.msgOps.recv.value);  // observe
          assert !InFlight(c, v', step.msgOps.recv.value);  // observe
        }
        assert Inv(c, v'); // observe
      } else {
        var recipient :| Host.DoGrant(c.hosts[step.id], v.hosts[step.id], v'.hosts[step.id], step.msgOps, recipient); // observe
        assert Inv(c, v'); // observe
      }
    }
//#end-elide
  }
}
