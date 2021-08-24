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
//#exercise  datatype Message = Message(/* FILL ME IN! */)
//#start-elide
  datatype Message = Grant(dest:HostId, epoch:nat)
//#end-elide

  // Define your Host protocol state machine here.
  datatype Constants = Constants(myId:HostId) {
    // host constants coupled to DistributedSystem Constants:
    // DistributedSystem tells us our id so we can recognize inbound messages.
    // TODO(jonh): get rid of ValidHosts; move hostCount in here instead.
    predicate GroupWF(id:HostId) {
      myId == id
    }
  }
//#exercise  datatype Variables = Variables(/* FILL ME IN! */)
//#start-elide
  datatype Variables = Variables(holdsLock:bool, epoch:nat)
//#end-elide

  predicate Init(c:Constants, v:Variables) {
//#exercise    true // Replace me
//#start-elide
    && v.holdsLock == (c.myId == 0)
    && v.epoch == if c.myId == 0 then 1 else 0
//#end-elide
  }

//#start-elide
  predicate DoGrant(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, recipient:HostId) {
    && v.holdsLock == true
    && msgOps.recv.None?
    && ValidHostId(recipient) // Doesn't actually affect safety, but does affect liveness! if we grant to msgOps nonexistent host, no further steps will occur.
    && msgOps.send == Some(Grant(recipient, v.epoch + 1))
    && v'.holdsLock == false
    && v'.epoch == v.epoch
  }

  predicate DoAccept(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    && msgOps.recv.Some?
    && msgOps.recv.value.dest == c.myId
    && msgOps.recv.value.epoch > v.epoch
    && msgOps.send == None
    && v'.epoch == msgOps.recv.value.epoch
    && v'.holdsLock == true
  }

//#end-elide
  // JayNF
  datatype Step =
//#exercise    | SomeStep
//#start-elide
    | DoGrantStep(recipient: HostId)
    | DoAcceptStep
//#end-elide

  predicate NextStep(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>, step: Step) {
    match step
//#exercise       case SomeStep => true
//#start-elide
      case DoGrantStep(recipient) => DoGrant(c, v, v', msgOps, recipient)
      case DoAcceptStep => DoAccept(c, v, v', msgOps)
//#end-elide
  }

  predicate Next(c:Constants, v:Variables, v':Variables, msgOps:Network.MessageOps<Message>) {
    exists step :: NextStep(c, v, v', msgOps, step)
  }
}
