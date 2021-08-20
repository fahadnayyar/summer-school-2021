//#title DistributedSystem
//#desc DO NOT EDIT THIS FILE! It's a trusted file that specifies how hosts interact
//#desc with one another over the network.

include "protocol.i.dfy"

// Before we get here, caller must define a type Message that we'll
// use to instantiate network.s.dfy.

module DistributedSystem {
  datatype Constants = Constants(
    hostCount: int,
    hosts:map<HostId, HostVars>)

  datatype Variables = Variables(
    hosts:map<HostId, HostVars>,
    network:NetVars<Message>)

  predicate WFVars(v:Variables) {
    // We don't lose track of any of the hosts.
    && v.hosts.Keys == AllHosts()
  }

  predicate DistInit(v:Variables) {
    && WFVars(v)
    && (forall id :: HostInit(v.hosts[id], id))
    && NetInit(v.network)
  }

  predicate NextStep(v:Variables, v':Variables, id:HostId, a:NetAction<Message>) {
    && WFVars(v)
    && WFVars(v')
    && HostNext(id, v.hosts[id], v'.hosts[id], a)
    && (forall other :: other != id ==> v'.hosts[other] == v.hosts[other])
    && NetNext(v.network, v'.network, a)
  }

  predicate DistNext(v:Variables, v':Variables) {
    exists id, a :: NextStep(v, v', id, a)
  }
}
