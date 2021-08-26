//#title Application Correspondence with Synchronous Sharded KV Store
//#desc How do we prevent a nonsense refinement theorem, for example one that does whatever
//#desc it wants, but abstracts every protocol-level state to the initial spec state, so it
//#desc can refine to a bunch of stutter steps?


// You are given datatypes to represent outstanding requests and completed
// replies waiting to be delivered to the client. Your task is to fill out the
// action predicates to model the asynchronous arrival of requests,
// serialization (moment of processing) points, and delivery of replies.

// Note that we're unconcerned with the protocol at the moment;
// the goal here is only to modify the spec to capture linearizability,
// a property that arises because client requests take time to process.

include "../../library/Library.dfy"

// See chapter06-refine/exercises/exercise01 for documentation on this module.
// (Here we give concrete types because we want to instantiatie the module for
// pseudoliveness tests at the end.)
module Types {
  type Key = string

  function AllKeys() : set<Key>
  {
    { "cat", "dog", "bird", "elephant" }
  }

  type Value = int

  function DefaultValue() : Value { 0 }

  function InitialMap() : map<Key, Value>
  {
    map key | key in AllKeys() :: DefaultValue()
  }

  // The Input and Output types describe the application-visible interface to the service.
  // The application chooses a nonce (so it can identify which replies belong to it --
  // think something like an RPC ID), and fills in the input parameters. The output reply
  // has a copy of the input (so the app can check the nonce) and any output result
  // (e.g. the value of a query).
  datatype Input =
    | InsertRequest(nonce:int, key:Key, value:Value)
    | QueryRequest(nonce:int, key:Key)

  datatype Output =
    | InsertReply(request: Input)
    | QueryReply(request: Input, output: Value)
}

// This module defines a Map state machine that serves as the system specification.
// In separate steps it should collect input requests from the client, service
// them atomically, then deliver output replies. Requests that are outstanding
// simultaneously can be serviced in any order (since the spec can
// nondeterministically select the order to service them); requests that don't
// overlap must affect each other in temporal order (linearizability).

module MapSpec {
  import opened Types

  datatype Variables = Variables(mapp:map<Key, Value>,
    requests:set<Input>, replies:set<Output>)
    //TODO(jonh) go to set; prevent duplicate insertion

  predicate Init(v: Variables)
  {
    && v.mapp == InitialMap()
    && v.requests == {}
    && v.replies == {}
  }

  predicate AcceptRequest(v:Variables, v':Variables, request: Input)
  {
    && request !in v.requests // (liveness only) if client picked identical nonces, don't let the requests collapse.
    && v' == v.(requests := v.requests + {request})
  }

  predicate DeliverReply(v:Variables, v':Variables, reply: Output)
  {
    && reply in v.replies
    && v' == v.(replies := v.replies - {reply})
  }

  predicate InsertOp(v:Variables, v':Variables, request: Input)
  {
    // A well-formed condition: we're not even gonna talk about keys other than AllKeys().
    && request.key in AllKeys()
    // Don't do a request that a client hasn't asked for.
    && request in v.requests
    && request.InsertRequest?
    && var reply := InsertReply(request);
    && reply !in v.replies  // (liveness only) if client picked identical nonces, don't let a reply "catch up" with another and collapse.
    && v' == v.(
      // Replace key with value. v.mapp domain remains AllKeys().
      mapp := v.mapp[request.key := request.value],
      // Remove request from those awaiting service
      requests := v.requests - {request},
      // Add reply marking Insert complete so client can learn about it
      replies := v.replies + {reply})
  }

  predicate QueryOp(v:Variables, v':Variables, request: Input, output: Value)
  {
    && request.key in AllKeys()
    && request.key in v.mapp
    // Don't do a request that a client hasn't asked for.
    && request in v.requests
    && request.QueryRequest?
    && var reply := QueryReply(request, output);
    && reply !in v.replies  // (liveness only) if client picked identical nonces, don't let a reply "catch up" with another and collapse.
    && output == v.mapp[request.key]
    && v' == v.(
      // (No change to mapp state)
      // Remove request from those awaiting service
      requests := v.requests - {request},
      // Add reply marking Insert complete so client can learn about it
      replies := v.replies + {reply})
  }

  datatype Step =
    | AcceptRequestStep(request:Input)
    | DeliverReplyStep(reply: Output)
    | InsertOpStep(request:Input)
    | QueryOpStep(request:Input, output:Value)
    | NoOpStep()

  predicate NextStep(v: Variables, v': Variables, step:Step)
  {
    match step
      case AcceptRequestStep(request) => AcceptRequest(v, v', request)
      case DeliverReplyStep(request) => DeliverReply(v, v', request)
      case InsertOpStep(request) => InsertOp(v, v', request)
      case QueryOpStep(request, output) => QueryOp(v, v', request, output)
      case NoOpStep => v' == v
  }

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
  }

  // Here are some point tests to confirm that the protocol allows various
  // desired behavior: two possible resulting states for runs with overlapping
  // insert requests, and one possible state for a run with non-overlapping
  // insert requests.

  // We'll materialize behaviors explicitly (as a sequence of states) so we can
  // goof around with proofs about what this spec might say.
  predicate ValidBehavior(execution:seq<Variables>, steps:seq<Step>)
  {
    && |execution| == |steps| + 1
    && Init(execution[0])
    && (forall i | 0<=i<|steps| :: NextStep(execution[i], execution[i+1], steps[i]))
  }

  lemma PseudoLiveness()
  {
    // Here's a run that orders a simultaneously-outstanding set of inserts one way.
    var req3 := InsertRequest(100, "cat", 3);
    var req4 := InsertRequest(101, "cat", 4);
    var executionA := [
      Variables(InitialMap(), {}, {}),
      Variables(InitialMap(), {req4}, {}),
      Variables(InitialMap(), {req3, req4}, {}),
      Variables(InitialMap()["cat" := 4], {req3}, {InsertReply(req4)}),
      Variables(InitialMap()["cat" := 3], {}, {InsertReply(req4), InsertReply(req3)}),
      Variables(InitialMap()["cat" := 3], {}, {InsertReply(req3)}),
      Variables(InitialMap()["cat" := 3], {}, {})
      ];
    var stepsA := [
      AcceptRequestStep(req4),
      AcceptRequestStep(req3),
      InsertOpStep(req4),
      InsertOpStep(req3),
      DeliverReplyStep(InsertReply(req4)),
      DeliverReplyStep(InsertReply(req3))
      ];
    assert ValidBehavior(executionA, stepsA);

    // Same outstanding requests, ordered the other way. Notice the state has a
    // different value for cat at the end. I could also actually *query* the
    // cat, but I'm too lazy.
    var executionB := [
      Variables(InitialMap(), {}, {}),
      Variables(InitialMap(), {req4}, {}),
      Variables(InitialMap(), {req3, req4}, {}),
      Variables(InitialMap()["cat" := 3], {req4}, {InsertReply(req3)}),
      Variables(InitialMap()["cat" := 4], {}, {InsertReply(req4), InsertReply(req3)}),
      Variables(InitialMap()["cat" := 4], {}, {InsertReply(req3)}),
      Variables(InitialMap()["cat" := 4], {}, {})
      ];
    var stepsB := [
      AcceptRequestStep(req4),
      AcceptRequestStep(req3),
      InsertOpStep(req3),
      InsertOpStep(req4),
      DeliverReplyStep(InsertReply(req4)),
      DeliverReplyStep(InsertReply(req3))
      ];
    assert ValidBehavior(executionB, stepsB);

  // Here one request completes before the other; only one outcome is possible.
    var executionC := [
      Variables(InitialMap(), {}, {}),
      Variables(InitialMap(), {req3}, {}),
      Variables(InitialMap()["cat" := 3], {}, {InsertReply(req3)}),
      Variables(InitialMap()["cat" := 3], {}, {}),
      Variables(InitialMap()["cat" := 3], {req4}, {}),
      Variables(InitialMap()["cat" := 4], {}, {InsertReply(req4)}),
      Variables(InitialMap()["cat" := 4], {}, {})
      ];
    var stepsC := [
      AcceptRequestStep(req3),
      InsertOpStep(req3),
      DeliverReplyStep(InsertReply(req3)),
      AcceptRequestStep(req4),
      InsertOpStep(req4),
      DeliverReplyStep(InsertReply(req4))
      ];
    assert ValidBehavior(executionC, stepsC);
  }
}

// This module is analogous to the network: it's a trusted module that gets connected to the
// host protocol via a binding variable. The host says "if the client were to initiate this request,
// here's how I'd respond;" this module gets to say "whether the client initiated this request".
// (Just as the network says whether a packet can be received.) This represents the trusted system
// "observing" requests crossing between the application and the protocol (eg at a library boundary),
// to ensure that the protocol proof isn't succeeding by simply lying.
module TrustedABI {
  import opened Library
  import opened Types

  datatype Constants = Constants()  // No constants
  datatype Variables = Variables(requests:set<Input>, replies:set<Output>)

  predicate Init(c: Constants, v: Variables)
  {
    && v.requests == {}
    && v.replies == {}
  }

  // Type of binding variable between Host and TrustedABI. Analogous to Network.MsgOps
  // While it expresses about the same freedom as MsgOps, no practical procotol could
  // remove a request and *not* return a reply and still hope to refine to MapSpec, since
  // MapSpec always replaces a request with a reply atomically.
  datatype ABIOps = ABIOps(request:Option<Input>, reply:Option<Output>)

  // Allow the Host to consume a request and produce a reply, if it wishes -- or
  // just do some background work (not used in this exercise).
  //
  // abiOps is a binding variable: protocol says what it'd do if it got that request,
  // and this module gets to say whether a request is available right now, or record
  // the fact that the protocol returned a given result.
  //
  // The Host protocol can drop any request it wants, and introduce any reply
  // it wants; that won't affect meaning, since it ultimately has to get the
  // incoming requests and outgoing replies to match what the spec allows.
  predicate ExecuteOp(c: Constants, v: Variables, v': Variables, abiOps: ABIOps)
  {
    && (abiOps.request.Some? ==>
        && abiOps.request.value in v.requests
        && v'.requests == v.requests - {abiOps.request.value})
    && (abiOps.reply.Some? ==>
        && abiOps.reply.value !in v.replies
        && v'.replies == v.replies + {abiOps.reply.value})
  }

  // Record the claim that a client actually made this request.
  // This corresponds to a trusted handler attesting that the client wanted the
  // request, it wasn't just invented by the protocol.
  predicate AcceptRequest(v:Variables, v':Variables, request: Input)
  {
    false // TODO Define this predicate. You're defining trusted bottom-bread spec now, so be careful!
  }

  // Ensure there's a reply to deliver to a client, and record the fact that
  // it's been delivered so we can't deliver a duplicate later.
  // This corresponds to a trusted handler attesting that this reply was
  // exposed to the client -- so the spec must justify the exposed value.
  predicate DeliverReply(v:Variables, v':Variables, reply: Output)
  {
    false // TODO Define this predicate. You're defining trusted bottom-bread spec now, so be careful!
  }

  // JayNF except "Next" is "ClientOp" -- one of two "entry points" to this module.
  datatype Step =
    | AcceptRequestStep(request:Input)
    | DeliverReplyStep(reply: Output)

  predicate ClientOpStep(c:Constants, v:Variables, v':Variables, step: Step)
  {
    match step
      case AcceptRequestStep(request) => AcceptRequest(v, v', request)
      case DeliverReplyStep(request) => DeliverReply(v, v', request)
  }

  predicate ClientOp(c:Constants, v:Variables, v':Variables)
  {
    exists step :: ClientOpStep(c, v, v', step)
  }
}

// This protocol definition began life as ShardedKVProtocol from
// chapter06-refine/solutions/exercise01.dfy. That exercise took a shortcut:
// rather that build a full-blown chapter05-style DistributedSystem,
// it modeled the set of hosts' maps as a seq of maps in a single state machine.
// So the first difference is that this Host contains a single map; the
// DistributedSystem module below it gathers up the set of several Hosts.
// That also means we have to split the single Transfer step (which atomically
// communicated a k,v pair from one host to another -- no network asynchrony)
// into separate Send and Recv actions, each of which runs on one Host, bound
// together by DistributedSystem.
// (TODO(jonh): Manos, think we should just fix all that stuff in ch06 for next
// time so this thing looks much closer? Yeah. We should.)
//
// The second difference, essential to this exercise, is that we introduce the
// connection to the client-visible Input requests and Output replies via a
// binding variable (abiOps) from the DistributedSystem. They capture the
// client asynchrony of chapter07, and are necessary to demonstrate application
// correspondence from this chapter.
//
// Note that, because this exercise takes the shortcut of having synchronous
// communication between Hosts (instead of the chapter05 Network model), we
// can't have a single Next "entry point" into Host. We use "Next" for the
// familiar case (one host takes a step, other hosts snooz), and then model
// synchronous communication with Send on one host and Recv on another.
module Host {
  import opened Library
  import opened Types
  import TrustedABI

  datatype Constants = Constants(myId: nat) {
    predicate GroupWF(id: nat) {
      && myId == id
    }
  }

  datatype Variables = Variables(mapp:map<Key, Value>)

  predicate Init(c: Constants, v: Variables)
  {
    v.mapp == if c.myId == 0 then InitialMap() else map[]
  }

  predicate Insert(c: Constants, v: Variables, v': Variables, abiOps: TrustedABI.ABIOps)
  {
    && abiOps.request.Some?
    && abiOps.request.value.InsertRequest?
    && var request := abiOps.request.value;
    && request.key in v.mapp // this host needs to be authoritative on this key
    && abiOps.reply == Some(InsertReply(request))
    && v' == v.(mapp := v.mapp[request.key := request.value])
  }

  predicate Query(c: Constants, v: Variables, v': Variables, abiOps: TrustedABI.ABIOps)
  {
    && abiOps.request.Some?
    && abiOps.request.value.QueryRequest?
    && abiOps.reply.Some?
    && abiOps.reply.value.QueryReply?
    && var request := abiOps.request.value;
    && var reply := abiOps.reply.value;
    && request.key in v.mapp // this host needs to be authoritative on this key
    && reply.request == request
    && reply.output == v.mapp[request.key]
    && v' == v
  }

  datatype Message = Transfer(key: Key, value: Value)

  // "Entry point" from DistributedSystem: send half of a synchronous message exchange with another host.
  predicate Send(c: Constants, v: Variables, v': Variables, msg: Message)
  {
    && msg.key in v.mapp
    && v.mapp[msg.key] == msg.value
    && v' == v.(mapp := MapRemoveOne(v.mapp, msg.key))  // key leaves sending map
  }

  // "Entry point" from DistributedSystem: receive half of a synchronous message exchange with another host.
  predicate Recv(c: Constants, v: Variables, v': Variables, msg: Message)
  {
    && v' == v.(mapp := v.mapp[msg.key := msg.value])  // key appears in recv map
  }

  // "Entry point" from DistributedSystem: Operate locally (no communication
  // with other Hosts). This may include processing a client request that's
  // waiting in the ABI -- a serialization point.
  // (We collapsed the JayNF here because, for this example, there's no
  // nondeterminism beyond what's already captured in abiOps.)
  predicate Next(c: Constants, v: Variables, v': Variables, abiOps: TrustedABI.ABIOps)
  {
    && abiOps.request.Some?
    && match abiOps.request.value
      case InsertRequest(_,_,_) => Insert(c, v, v', abiOps)
      case QueryRequest(_,_) => Query(c, v, v', abiOps)
  }
}

// This is the trusted distributed system compound state machine that ties
// copies of the untrusted Host protocol together with an instance of the
// TrustedABI state machine. Observe what kinds of interactions it allows -- in
// particular, convince yourself that Player 2 can't synthesize a client Request
// from whole cloth; the TrustedABI has to do that.
//
// We ask you to define ClientOp -- the step where a request arrives to or
// reply is deliverd from the TrustedABI, and the Hosts aren't allowed to touch
// anything.
module DistributedSystem {
  import Host
  import TrustedABI

  type HostIdx = nat

  datatype Constants = Constants(hosts: seq<Host.Constants>, abi: TrustedABI.Constants)
  {
    predicate ValidHost(idx: HostIdx) {
      idx < |hosts|
    }
    predicate WF() {
      && 0 < |hosts|
      && (forall idx:HostIdx | ValidHost(idx) :: hosts[idx].GroupWF(idx)) // configure hosts with their id
    }
  }

  datatype Variables = Variables(hosts: seq<Host.Variables>, abi: TrustedABI.Variables)
  {
    predicate WF(c: Constants) {
      && c.WF()
      && |hosts| == |c.hosts|
    }
  }

  predicate Init(c:Constants, v:Variables)
  {
    && v.WF(c)
    && (forall idx:HostIdx | c.ValidHost(idx) :: Host.Init(c.hosts[idx], v.hosts[idx]))
    && TrustedABI.Init(c.abi, v.abi)
  }

  // Have ABI module record an incoming request or delivers a reply;
  // no host does anything.
  predicate ClientOp(c:Constants, v:Variables, v':Variables)
  {
    false // TODO Define this predicate. You're defining trusted bottom-bread spec now, so be careful!
  }

  // Because we're cheating with a synchronous network model, this trusted
  // DistributedSystem model needs to be aware of how the protocol does
  // transfers (because two hosts are involved) versus other steps (one host at
  // a time). To keep it simple, we'll disallow interacting with the client
  // during a communicate step. Just as with the usual Network model, the
  // protocol (Host module) gets to define its message type.
  predicate Communicate(c: Constants, v: Variables, v':Variables, sendIdx:HostIdx, recvIdx:HostIdx, msg:Host.Message)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHost(sendIdx)
    && c.ValidHost(recvIdx)
    && Host.Send(c.hosts[sendIdx], v.hosts[sendIdx], v'.hosts[sendIdx], msg)
    && Host.Recv(c.hosts[recvIdx], v.hosts[recvIdx], v'.hosts[recvIdx], msg)
    && (forall otherIdx:HostIdx | c.ValidHost(otherIdx) && otherIdx != sendIdx && otherIdx != recvIdx
          :: v'.hosts[otherIdx] == v.hosts[otherIdx])
    && v'.abi == v.abi  // UNCHANGED
  }

  predicate OneHost(c: Constants, v: Variables, v':Variables, hostIdx:HostIdx, abiOps: TrustedABI.ABIOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHost(hostIdx)
    && Host.Next(c.hosts[hostIdx], v.hosts[hostIdx], v'.hosts[hostIdx], abiOps)
    && (forall otherIdx:HostIdx | c.ValidHost(otherIdx) && otherIdx != hostIdx :: v'.hosts[otherIdx] == v.hosts[otherIdx])
    && TrustedABI.ExecuteOp(c.abi, v.abi, v'.abi, abiOps)
  }

  datatype Step =
    | ClientOpStep
    | CommunicateStep(sendIdx: HostIdx, recvIdx: HostIdx, msg: Host.Message)
    | OneHostStep(hostIdx: HostIdx, abiOps: TrustedABI.ABIOps)

  predicate NextStep(c: Constants, v: Variables, v':Variables, step: Step)
  {
    match step
      case ClientOpStep => ClientOp(c, v, v')
      case CommunicateStep(sendIdx, recvIdx, msg) => Communicate(c, v, v', sendIdx, recvIdx, msg)
      case OneHostStep(hostIdx, abiOps) => OneHost(c, v, v', hostIdx, abiOps)
  }

  predicate Next(c: Constants, v: Variables, v':Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}

// This proof began life as the solution to chapter06/exercises/exercise06.dfy.
// Rejiggering the protocol model to be a DistributedSystem compound state
// machine entailed making a bunch of boring search-replace syntax changes to the
// text below, which we did for you -- try diffing it against that solution.
// That change also interfered with a bit of automation; read the comment above
// the newly introduced lemma EqualMapsEqualKeysHeldUniquely to understand what
// happened.
// Finally, the chapter06 proof predates chapter07's introduction of the
// AcceptRequest and DeliverReply steps that model client asynchrony in both
// the spec (chapter07) and the protocol (here).
//
// Your jobs: update the Abstraction function, plus there's a hole in the proof
// below with a TODO marked; fill it in.
module RefinementProof {
  import opened Library
  import opened Types
  import MapSpec
  import opened DistributedSystem

  predicate HostHasKey(c: Constants, v: Variables, hostidx:HostIdx, key:Key)
    requires v.WF(c)
  {
    && c.ValidHost(hostidx)
    && key in v.hosts[hostidx].mapp
  }

  // Pulling the choose out into its own function is sometimes necessary due
  // to a (deliberate) stupidity in Dafny: it doesn't treat :| expressions
  // as subsitution-equivalent, even though the are (as evidenced by pulling
  // one into a function).
  function KeyHolder(c: Constants, v: Variables, key:Key) : HostIdx
    requires v.WF(c)
    requires exists hostidx :: HostHasKey(c, v, hostidx, key)
  {
    var hostidx:HostIdx :| HostHasKey(c, v, hostidx, key);
    hostidx
  }


  function AbstractionOneKey(c: Constants, v: Variables, key:Key) : Value
    requires v.WF(c)
  {
    if exists idx :: HostHasKey(c, v, idx, key)
    then
      v.hosts[KeyHolder(c, v, key)].mapp[key]
    else DefaultValue()
  }

  // We construct the finite set of possible map keys here, all
  // because we need to supply Dafny with simple evidence that our map domain
  // is finite for the map comprehension in Abstraction().
  // (An alternative would be to switch to imaps -- maps with potentially-infinite
  // domains -- but that would require making the spec fancier. This was a compromise.)

  // The sequence of map domains. Pulled out into its own function to
  // make proof assertions easy to write.
  function MapDomains(c: Constants, v: Variables) : seq<set<Key>>
    requires v.WF(c)
  {
    seq(|c.hosts|, i requires 0<=i<|c.hosts| => v.hosts[i].mapp.Keys)
  }

  function KnownKeys(c: Constants, v: Variables) : set<Key>
    requires v.WF(c)
  {
    UnionSeqOfSets(MapDomains(c, v))
  }

  // Packaged as lemma. Proves trivially as ensures of KnownKeys,
  // but creates a trigger storm.
  lemma HostKeysSubsetOfKnownKeys(c: Constants, v: Variables, count: nat)
    requires v.WF(c)
    requires count <= |c.hosts|
    ensures forall idx | 0 <= idx < count :: v.hosts[idx].mapp.Keys <= KnownKeys(c, v)
  {
    forall idx | 0 <= idx < count ensures v.hosts[idx].mapp.Keys <= KnownKeys(c, v)
    {
      SetsAreSubsetsOfUnion(MapDomains(c, v));
      assert v.hosts[idx].mapp.Keys == MapDomains(c, v)[idx];  // trigger
    }
  }

  function Abstraction(c: Constants, v: Variables) : MapSpec.Variables
    requires v.WF(c)
  {
    MapSpec.Variables(
      map key | key in KnownKeys(c, v) :: AbstractionOneKey(c, v, key),
      {}, {})  // TODO that's not gonna work. Abstract appropriately.
  }

  // This definition is useful, but a bit trigger-happy, so we made it
  // opaque. This means that its body is hidden from Dafny, unless you
  // explicitly write "reveal_KeysHeldUniquely();", at which point the
  // body of the predicate becomes available within the current context
  predicate {:opaque} KeysHeldUniquely(c: Constants, v: Variables)
    requires v.WF(c)
  {
    forall key, hostidx:HostIdx, otherhost:HostIdx
        | && c.ValidHost(hostidx) && c.ValidHost(otherhost)
          && key in v.hosts[hostidx].mapp && key in v.hosts[otherhost].mapp
        :: hostidx == otherhost
  }

  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
    // Every key lives somewhere.
    && KnownKeys(c, v) == Types.AllKeys()
    // No key lives in two places.
    && KeysHeldUniquely(c, v)
  }

  lemma InitAllKeysEmpty(c: Constants, v: Variables, count: nat)
    requires Init(c, v)
    requires 0 < count <= |c.hosts|
    ensures KnownKeys(c, v) == AllKeys()
  {
    EachUnionMemberBelongsToASet(MapDomains(c, v));
    SetsAreSubsetsOfUnion(MapDomains(c, v));
    forall key | key in AllKeys() ensures key in KnownKeys(c, v) {
      assert key in MapDomains(c,v)[0]; // trigger
    }
  }

  lemma RefinementInit(c: Constants, v: Variables)
    requires c.WF()
    requires Init(c, v)
    ensures MapSpec.Init(Abstraction(c, v))
    ensures Inv(c, v)
  {
    InitAllKeysEmpty(c, v, |c.hosts|);
    reveal_KeysHeldUniquely();
  }

  // Since we know that keys are held uniquely, if we've found a host that holds a key,
  // that can be the only solution to the 'choose' operation that defines KeyHolder.
  lemma AnyHostWithKeyIsKeyHolder(c: Constants, v: Variables, hostidx:HostIdx, key:Key)
    requires v.WF(c)
    requires KeysHeldUniquely(c, v)
    requires HostHasKey(c, v, hostidx, key)
    ensures KeyHolder(c, v, key) == hostidx
  {
    reveal_KeysHeldUniquely();
  }

  // This is not a goal by itself, it's one of the cases you'll need to prove
  // NextPreservesInvAndRefines. We've provided its signature to help you
  // structure your overall proof.
  lemma InsertPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, hostIdx: HostIdx, abiOps: TrustedABI.ABIOps)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(hostIdx)
    requires OneHost(c, v, v', hostIdx, abiOps)
    requires Host.Insert(c.hosts[hostIdx], v.hosts[hostIdx], v'.hosts[hostIdx], abiOps)
    ensures Inv(c, v')
    ensures MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.InsertOpStep(abiOps.request.value))
  {
    var abstractMap := Abstraction(c, v).mapp;
    var abstractMap' := Abstraction(c, v').mapp;
    var request := abiOps.request.value;
    var insertedKey := request.key; // use some let-in assignments to recycle chapter06 proof...
    var value := request.value;

    assert insertedKey in AllKeys() by {
      SetsAreSubsetsOfUnion(MapDomains(c, v));
      assert MapDomains(c, v)[hostIdx] == v.hosts[hostIdx].mapp.Keys; //trigger
    }

    assert KeysHeldUniquely(c, v') by { reveal_KeysHeldUniquely(); }

    forall key
      ensures key in abstractMap' <==> key in abstractMap || key == insertedKey // domain
      ensures key in abstractMap' ==> (abstractMap'[key] == if key==insertedKey then value else abstractMap[key])  // value
    {
      if key == insertedKey {
        SetsAreSubsetsOfUnion(MapDomains(c, v'));
        assert MapDomains(c, v')[hostIdx] <= KnownKeys(c, v'); // trigger
        assert key in abstractMap'; // case goal
      }
      if key in abstractMap {
        var idx := GetIndexForMember(MapDomains(c, v), key);
        assert MapDomains(c, v')[idx] <= KnownKeys(c, v') by {
          // The lemma below is a trigger-trap danger (causes timeouts), so I'm
          // careful to only call it tucked way into this by clause.
          SetsAreSubsetsOfUnion(MapDomains(c, v'));
        }
        assert key in abstractMap'; // case goal
      }
      if key in abstractMap' {
        if key == insertedKey {
          AnyHostWithKeyIsKeyHolder(c, v', hostIdx, key);
          assert abstractMap'[key] == value;  // case goal
        } else {
          var keyIdx := GetIndexForMember(MapDomains(c, v'), key);
          AnyHostWithKeyIsKeyHolder(c, v', keyIdx, key);
          AnyHostWithKeyIsKeyHolder(c, v, keyIdx, key);
          assert key in abstractMap by {
            SetsAreSubsetsOfUnion(MapDomains(c, v));
            assert MapDomains(c, v)[keyIdx] <= KnownKeys(c, v);  // trigger
          }
          assert abstractMap'[key] == abstractMap[key]; // case goal
        }
      }
    }

    assert KnownKeys(c, v') == Types.AllKeys() by {
      assert abstractMap'.Keys == KnownKeys(c, v'); // trigger
    }
    assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.InsertOpStep(abiOps.request.value));
  }

  lemma ExistsHostHasKey(c:Constants, v:Variables, key:Key)
    requires Inv(c, v)
    requires key in KnownKeys(c, v);
    ensures exists hostidx :: HostHasKey(c, v, hostidx, key)
  {
    EachUnionMemberBelongsToASet(MapDomains(c, v));
    var idx :| 0<=idx<|c.hosts| && key in MapDomains(c, v)[idx];
    assert HostHasKey(c, v, idx, key);
  }

  // This proof's interaction with automation gets a little clumsier with the
  // addition of new fields to AsyncClientShardedKVProtocol.Variables. In
  // chapter06, if v'.maps==v.maps, then v'==v, so it knew
  // KeysHeldUniquely(v')==KeysHeldUniquely(v') just by substitution, even
  // thought it couldn't see inside that predicate because it's {:opaque}.
  // Now, an operation like Query leaves the hosts' maps unchanged, but v'!=v
  // because we fiddled with v.abi (requests and replies), and Dafny can't tell
  // that the predicate is identical.
  // The instructors' minimal-edit solution was to prove these lemmas and use
  // them as needed.
  // Another more elegant possibility would be to redefine KeysHeldUniquely and
  // related functions to only accept the hosts (and hence their maps) field as
  // an argument, so that Dafny could continue reasoning about them using only
  // substitution. That would entail plumbing through some new
  // hosts-seq-specific WF conditions as well.
  lemma EqualMapsEqualKeysHeldUniquely(c: Constants, v: Variables, v': Variables)
    requires v.WF(c)
    requires v'.WF(c)
    requires v'.hosts == v.hosts
    ensures KeysHeldUniquely(c, v') == KeysHeldUniquely(c, v)
  {
    reveal_KeysHeldUniquely();
  }

  lemma EqualMapsEqualMapp(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Inv(c, v')
    requires v'.hosts == v.hosts
    ensures Abstraction(c, v').mapp == Abstraction(c, v).mapp
  {
    forall k | k in Abstraction(c, v').mapp ensures Abstraction(c, v').mapp[k] == Abstraction(c, v).mapp[k] {
      ExistsHostHasKey(c, v', k);
      ExistsHostHasKey(c, v, k);
      assert KeyHolder(c, v', k) == KeyHolder(c, v, k) by { reveal_KeysHeldUniquely(); }
    }
  }

  // This is not a goal by itself, it's one of the cases you'll need to prove
  // NextPreservesInvAndRefines. We've provided its signature to help you
  // structure your overall proof.
  lemma QueryPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, hostIdx: HostIdx, abiOps: TrustedABI.ABIOps)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(hostIdx)
    requires v'.WF(c)
    requires OneHost(c, v, v', hostIdx, abiOps)
    requires Host.Query(c.hosts[hostIdx], v.hosts[hostIdx], v'.hosts[hostIdx], abiOps)
    ensures Inv(c, v')
    ensures MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.QueryOpStep(abiOps.request.value, abiOps.reply.value.output))
  {
    var request := abiOps.request.value;
    var key := request.key;
    assert v.hosts == v'.hosts; // weirdly obvious trigger
    assert Inv(c, v') by { reveal_KeysHeldUniquely(); }
    assert key in KnownKeys(c, v) by { HostKeysSubsetOfKnownKeys(c, v, |c.hosts|); }
    assert abiOps.reply.value.output == Abstraction(c, v).mapp[key] by {
      assert HostHasKey(c, v, hostIdx, key);  // witness
      reveal_KeysHeldUniquely();
    }
    EqualMapsEqualMapp(c, v, v');
  }

  // This is not a goal by itself, it's one of the cases you'll need to prove
  // NextPreservesInvAndRefines. We've provided its signature to help you
  // structure your overall proof.
  lemma TransferPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, sendIdx: HostIdx, recvIdx: HostIdx, msg:Host.Message)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(sendIdx)
    requires c.ValidHost(recvIdx)
    requires Host.Send(c.hosts[sendIdx], v.hosts[sendIdx], v'.hosts[sendIdx], msg)
    requires Host.Recv(c.hosts[recvIdx], v.hosts[recvIdx], v'.hosts[recvIdx], msg)
    ensures Inv(c, v')
    ensures MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.NoOpStep)
  {
    // domain preserved
    forall key
      ensures key in Abstraction(c, v).mapp <==> key in Abstraction(c, v').mapp
    {
      var idx;
      if key in Abstraction(c, v).mapp {
        SetsAreSubsetsOfUnion(MapDomains(c, v'));
        if key==msg.key {
          idx := recvIdx;
        }
        else {
          idx := GetIndexForMember(MapDomains(c, v), key);
        }
        assert MapDomains(c, v')[idx] <= KnownKeys(c, v');  // trigger
        assert key in Abstraction(c, v').mapp;  // case goal
      }
      if key in Abstraction(c, v').mapp {
        SetsAreSubsetsOfUnion(MapDomains(c, v));
        if key==msg.key {
          idx := sendIdx;
        }
        else {
          idx := GetIndexForMember(MapDomains(c, v'), key);
        }
        assert MapDomains(c, v)[idx] <= KnownKeys(c, v);  // trigger
        assert key in Abstraction(c, v).mapp;  // case goal
      }
    }

    assert KeysHeldUniquely(c, v') by { reveal_KeysHeldUniquely(); }

    // values preserved
    forall key | key in Abstraction(c, v).mapp
      ensures Abstraction(c, v).mapp[key] == Abstraction(c, v').mapp[key]
    {
      // identify where to find key in the old & new worlds
      var idx, idx';
      if key == msg.key {
        idx := sendIdx;
        idx' := recvIdx;
      } else {
        idx := GetIndexForMember(MapDomains(c, v), key);
        idx' := idx;
      }
//      assert v'.maps[idx'][key] == v.maps[idx][key];  // hey look same values

      // Tie from particular map up to abstraction
      AnyHostWithKeyIsKeyHolder(c, v', idx', key);
      AnyHostWithKeyIsKeyHolder(c, v, idx, key);
    }

    assert KnownKeys(c, v') == Types.AllKeys() by {
      assert KnownKeys(c, v') == Abstraction(c, v').mapp.Keys;  // trigger
      assert KnownKeys(c, v) == Abstraction(c, v).mapp.Keys;    // trigger
    }
  }

  // Player 2 can define any Abstraction function they want, but it must
  // synchronize the application-visible requests and replies from the
  // protocol-level ABI to the spec-level model.
  // Unless you're trying to trick Player 1, this lemma should prove without help.
  lemma RefinementHonorsApplicationCorrespondence(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Abstraction(c, v).requests == v.abi.requests
    ensures Abstraction(c, v).replies == v.abi.replies
  {
  }

  lemma RefinementNext(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
    // Use InsertPreservesInvAndRefines, QueryPreservesInvAndRefines, and
    // TransferPreservesInvAndRefines here to complete this proof.
    var step :| NextStep(c, v, v', step);
    match step
      case ClientOpStep => {
        EqualMapsEqualKeysHeldUniquely(c, v, v');
        EqualMapsEqualMapp(c, v, v');
        // TODO New proof needed for new ClientOpStep -- witnesses to corresponding new MapSpec steps.
      }
      case CommunicateStep(sendIdx, recvIdx, msg) => {
        TransferPreservesInvAndRefines(c, v, v', sendIdx, recvIdx, msg);
      }
      case OneHostStep(hostIdx, abiOps) => {
        match abiOps.request.value
          case InsertRequest(_,_,_) => {
            InsertPreservesInvAndRefines(c, v, v', hostIdx, abiOps);
          }
          case QueryRequest(_,_) => {
            QueryPreservesInvAndRefines(c, v, v', hostIdx, abiOps);
          }
      }
  }
}
