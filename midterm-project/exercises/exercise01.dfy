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

module SafetySpec {
  import opened HostIdentifiers
  import DistributedSystem

  // No two hosts think they hold the lock simulatneously.
  predicate Safety(c:DistributedSystem.Constants, v:DistributedSystem.Variables) {
    false // Replace this placeholder with an appropriate safety condition: no two clients hold
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
    && false // ...and then add a check that the message's epoch is still valid.
  }


  predicate Inv(c: Constants, v:Variables) {
    true // Replace this placeholder with an invariant that's inductive and supports Safety.
  }

  lemma SafetyProof(c: Constants, v:Variables, v':Variables)
    ensures Init(c, v) ==> Inv(c, v)
    ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
    ensures Inv(c, v) ==> Safety(c, v)
  {
    // Develop any necessary proof here.
  }
}
