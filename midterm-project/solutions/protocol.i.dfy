//#title Protocol file
//#desc Define your protocol implementation here: message type, state machine

include "network.s.dfy"

module Host {
  import opened HostIdentifiers
  import Network

  // Define your Message datatype here.
  //#exercisedatatype Message = Message(/* FILL ME IN! */)
  //#start-elide
  datatype Message = Grant(dest:HostId, epoch:nat)
  //#end-elide

  // Define your Host protocol state machine here.
  //#exercisedatatype HostVars = HostVars(/* FILL ME IN! */)
  //#start-elide
  datatype HostVars = HostVars(holdsLock:bool, epoch:nat)
  //#end-elide

  predicate Init(v:HostVars, id:HostId) {
  //#exercise  true // Replace me
  //#start-elide
    && v.holdsLock == (id == 0)
    && v.epoch == if id == 0 then 1 else 0
  //#end-elide
  }

  //#start-elide
  predicate DoGrant(v:HostVars, v':HostVars, a:Network.MessageOps<Message>, recipient:HostId) {
    && v.holdsLock == true
    && a.rcv.None?
    && a.send == {Grant(recipient, v.epoch + 1)}
    && v'.holdsLock == false
    && v'.epoch == v.epoch
  }

  predicate DoAccept(id:HostId, v:HostVars, v':HostVars, a:Network.MessageOps<Message>) {
    && a.rcv.Some?
    && a.rcv.value.dest == id
    && a.rcv.value.epoch > v.epoch
    && a.send == {}
    && v'.epoch == a.rcv.value.epoch
    && v'.holdsLock == true
  }

  //#end-elide
  // The (trusted) DistributedSystem helpfully tells the host what its id is,
  // so the host can tell which messages are addressed to it. In a real system,
  // that id would be a constant part of the hosts' state; here we're trying
  // to keep the boilerplate to a minimum.
  predicate Next(id:HostId, v:HostVars, v':HostVars, a:Network.MessageOps<Message>) {
  //#exercise  true // Replace me
  //#start-elide
    || (exists recipient :: DoGrant(v, v', a, recipient) )
    || DoAccept(id, v, v', a)
  //#end-elide
  }
}
