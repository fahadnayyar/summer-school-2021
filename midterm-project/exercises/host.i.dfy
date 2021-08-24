//#title Host protocol
//#desc Define the host state machine here: message type, state machine for executing one
//#desc host's part of the protocol.

// See exercise01.dfy for an English design of the protocol.

include "network.s.dfy"

module Host {
  import opened Library
  import opened HostIdentifiers
  import Network

  // Define your Message datatype here.
  datatype Message = Message(/* FILL ME IN! */)

  // Define your Host protocol state machine here.
  datatype Constants = Constants(myId:HostId) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    // TODO(jonh): get rid of ValidHosts; move hostCount in here instead.
    predicate GroupWF(id:HostId) {
      myId == id
    }
  }
  datatype Variables = Variables(/* FILL ME IN! */)

  predicate Init(c:Constants, v:Variables) {
    true // Replace me
  }

  // JayNF
  datatype Step =
    | SomeStep

  predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
       case SomeStep => true
  }

  predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
