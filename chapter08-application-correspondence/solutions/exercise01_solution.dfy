//#title Application Correspondence with Synchronous Sharded KV Store
//#desc How do we prevent a nonsense refinement theorem, for example one that does whatever
//#desc it wants, but abstracts every protocol-level state to the initial spec state, so it
//#desc can refine to a bunch of stutter steps?

include "../../chapter07-async-clients/solutions/exercise01_solution.dfy" //#magicinline

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
  datatype ABIOps =
    | ServiceRequestOp(request:Input, reply:Output)
    | NoOp

  // 
  // abiOps is a binding variable: protocol says what it'd do if it got that request,
  // and this module gets to say whether a request is available right now, or record
  // the fact that the protocol returned a given result.
  predicate ExecuteOp(c: Constants, v: Variables, v': Variables, abiOps: ABIOps)
  {
    match abiOps
      case ServiceRequestOp(request, reply) =>
        // Protocol can drop any request it wants, and introduce any reply it
        // wants; that won't affect meaning, since it ultimately has to get the
        // incoming requests and outgoing replies to match what the spec
        // allows.
        && abiOps.request in v.requests
        && abiOps.reply !in v.replies
        && v' == v.(requests := v.requests - {abiOps.request}, replies := v.replies + {abiOps.reply})
      case NoOp() =>
        && v' == v
  }

  // Record the claim that a client actually made this request. This
  // corresponds to a trusted handler attesting that the client wanted
  // the request, it wasn't just invented by the protocol.
  predicate AcceptRequest(v:Variables, v':Variables, request: Input)
  {
//#exercise    false // TODO Define this predicate
//#start-elide
    && request !in v.requests
    && v' == v.(requests := v.requests + {request})
//#end-elide
  }

  // Record the fact that the client learned this reply. This corresponds
  // to a trusted handler attesting that this reply was exposed to the
  // client -- so the spec had better justify the exposed value.
  predicate DeliverReply(v:Variables, v':Variables, reply: Output)
  {
//#exercise    false // TODO Define this predicate
//#start-elide
    && reply in v.replies
    && v' == v.(replies := v.replies - {reply})
//#end-elide
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

// For reference, go see your or the instructors' solution to chapter06-refine/exercises/exercise01.dfy
// Note that, in this version, we split up the seq<map> into separate Host state machines (which then
// there are a seq of in the DistributedSystem), so it feels closer to our canonical compound
// state machine module of a distributed system. However, to keep this example simple, we still use
// synchronous communication among hosts (not an asynchronous network).
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
    && abiOps.ServiceRequestOp?
    && abiOps.request.InsertRequest?
    && abiOps.request.key in v.mapp // this host needs to be authoritative on this key
    && abiOps.reply == InsertReply(abiOps.request)
    && v' == v.(mapp := v.mapp[abiOps.request.key := abiOps.request.value])
  }

  predicate Query(c: Constants, v: Variables, v': Variables, abiOps: TrustedABI.ABIOps)
  {
    && abiOps.ServiceRequestOp?
    && abiOps.request.QueryRequest?
    && abiOps.request.key in v.mapp // this host needs to be authoritative on this key
    && abiOps.reply.QueryReply?
    && abiOps.reply.request == abiOps.request
    && abiOps.reply.output == v.mapp[abiOps.request.key]
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

  // "Entry point" from DistributedSystem: process a client request that's waiting in the ABI -- a serialization point.
  predicate Local(c: Constants, v: Variables, v': Variables, abiOps: TrustedABI.ABIOps)
  {
    && abiOps.ServiceRequestOp? // We don't have any NoOp Local ops. (Send/Recv is an ABI noop, but it's not Local)
    && match abiOps.request
      case InsertRequest(_,_,_) => Insert(c, v, v', abiOps)
      case QueryRequest(_,_) => Query(c, v, v', abiOps)
  }
}

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

  // ABI records an incoming request or delivers a reply
  predicate ClientOp(c:Constants, v:Variables, v':Variables)
  {
//#exercise    false // TODO Define this predicate
//#start-elide
    && v.WF(c)
    && v'.WF(c)
    && TrustedABI.ClientOp(c.abi, v.abi, v'.abi)
    && (forall hostIdx:HostIdx | c.ValidHost(hostIdx) :: v'.hosts[hostIdx] == v.hosts[hostIdx])
//#end-elide
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

  predicate Local(c: Constants, v: Variables, v':Variables, hostIdx:HostIdx, abiOps: TrustedABI.ABIOps)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHost(hostIdx)
    && Host.Local(c.hosts[hostIdx], v.hosts[hostIdx], v'.hosts[hostIdx], abiOps)
    && (forall otherIdx:HostIdx | c.ValidHost(otherIdx) && otherIdx != hostIdx :: v'.hosts[otherIdx] == v.hosts[otherIdx])
    && TrustedABI.ExecuteOp(c.abi, v.abi, v'.abi, abiOps)
  }

  datatype Step =
    | ClientOpStep
    | CommunicateStep(sendIdx: HostIdx, recvIdx: HostIdx, msg: Host.Message)
    | LocalStep(hostIdx: HostIdx, abiOps: TrustedABI.ABIOps)

  predicate NextStep(c: Constants, v: Variables, v':Variables, step: Step)
  {
    match step
      case ClientOpStep => ClientOp(c, v, v')
      case CommunicateStep(sendIdx, recvIdx, msg) => Communicate(c, v, v', sendIdx, recvIdx, msg)
      case LocalStep(hostIdx, abiOps) => Local(c, v, v', hostIdx, abiOps)
  }

  predicate Next(c: Constants, v: Variables, v':Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}

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
//#exercise    DefaultValue() // Replace me
//#start-elide
    if exists idx :: HostHasKey(c, v, idx, key)
    then
      v.hosts[KeyHolder(c, v, key)].mapp[key]
    else DefaultValue()
//#end-elide
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
//#exercise    MapSpec.Variables(InitialMap()) // Replace me
//#start-elide
    MapSpec.Variables(
      map key | key in KnownKeys(c, v) :: AbstractionOneKey(c, v, key),
      v.abi.requests,
      v.abi.replies)
//#end-elide
  }

//#elide  // This does slow things down quite a bit.
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
//#exercise    false // Replace me
//#start-elide
    && v.WF(c)
    // Every key lives somewhere.
    && KnownKeys(c, v) == Types.AllKeys()
    // No key lives in two places.
    && KeysHeldUniquely(c, v)
//#end-elide
  }

//#start-elide
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

//#end-elide
  lemma RefinementInit(c: Constants, v: Variables)
    requires c.WF()
    requires Init(c, v)
    ensures MapSpec.Init(Abstraction(c, v))
    ensures Inv(c, v)
  {
//#start-elide
    InitAllKeysEmpty(c, v, |c.hosts|);
    reveal_KeysHeldUniquely();
//#end-elide
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
    requires Local(c, v, v', hostIdx, abiOps)
    requires Host.Insert(c.hosts[hostIdx], v.hosts[hostIdx], v'.hosts[hostIdx], abiOps)
    ensures Inv(c, v')
    ensures MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.InsertOpStep(abiOps.request))
  {
//#start-elide
    var abstractMap := Abstraction(c, v).mapp;
    var abstractMap' := Abstraction(c, v').mapp;
    var request := abiOps.request;
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
    assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.InsertOpStep(abiOps.request));
//#end-elide
  }

  lemma ExistsHostHasKey(c:Constants, v:Variables, key:Key)
    requires Inv(c, v)
    requires key in KnownKeys(c, v);
    ensures exists hostidx :: HostHasKey(c, v, hostidx, key)
  {
    EachUnionMemberBelongsToASet(MapDomains(c, v));
//    assert key in UnionSeqOfSets(MapDomains(c, v));
//    assert exists idx :: 0<=idx<c.mapCount && key in MapDomains(c, v)[idx];
    var idx :| 0<=idx<|c.hosts| && key in MapDomains(c, v)[idx];
    assert HostHasKey(c, v, idx, key);
  }

  // This proof's interaction with automation gets a little clumsier with the
  // addition of new fields to AsyncClientShardedKVProtocol.Variables. In
  // chapter06, if v'.maps==v.maps, then v'==v, so it knew
  // KeysHeldUniquely(v')==KeysHeldUniquely(v') just by substitution, even
  // thought it couldn't see inside that predicate because it's {:opaque}.  Now
  // we can have equal maps, but v'!=v because we fiddled with the
  // requests/replies fields (as in Query), and Dafny can't tell that the
  // predicate is identical.
  // The instructors' minimal-edit solution was to prove these lemmas and use
  // them as needed.
  // Another more elegant possibility would be to redefine KeysHeldUniquely and
  // related functions to only accept the maps field as an argument, so that
  // Dafny could continue reasoning about them using only substitution. That
  // would entail plumbing through some new maps-specific WF conditions as well.
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
    requires Local(c, v, v', hostIdx, abiOps)
    requires Host.Query(c.hosts[hostIdx], v.hosts[hostIdx], v'.hosts[hostIdx], abiOps)
    ensures Inv(c, v')
    ensures MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.QueryOpStep(abiOps.request, abiOps.reply.output))
  {
//#start-elide
    var request := abiOps.request;
    var key := request.key;
    assert v.hosts == v'.hosts; // weirdly obvious trigger
    assert Inv(c, v') by { reveal_KeysHeldUniquely(); }
    assert key in KnownKeys(c, v) by { HostKeysSubsetOfKnownKeys(c, v, |c.hosts|); }
    assert abiOps.reply.output == Abstraction(c, v).mapp[key] by {
      assert HostHasKey(c, v, hostIdx, key);  // witness
      reveal_KeysHeldUniquely();
    }
    EqualMapsEqualMapp(c, v, v');
//#end-elide
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
//#start-elide
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
//#end-elide
  }

  // Player 2 can define any Abstraction function they want, but it must
  // synchronize the application-visible requests and replies from the
  // protocol-level ABI to the spec-level model.
  lemma RefinementHonorsApplicationCorrespondence(c: Constants, v: Variables)
    requires Inv(c, v)
    // It's wonky that we have to look inside the untrusted 'v' to find the abi state,
    // but that's a consequence of the wonky choice of tucking the trusted ABI into the
    // protocol module, rather than having a trusted DistributedSystem that contains
    // the untrusted host protocol module; see comments above.
    ensures Abstraction(c, v).requests == v.abi.requests
    ensures Abstraction(c, v).replies == v.abi.replies
  {
  }

  // The proof goal is modified from chapter06 to expose the protocl- and
  // spec-level step objects so we can add an application-correspendence check
  // as an ensures. So where we used to just producte a witness to the application-level
  // step, we now have to actually return it to satisfy the lemmas' mentions of NextStep
  // (instead of just Next).
  lemma RefinementNext(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
    // Use InsertPreservesInvAndRefines, QueryPreservesInvAndRefines, and
    // TransferPreservesInvAndRefines here to complete this proof.
//#start-elide
    var av := Abstraction(c, v);
    var av' := Abstraction(c, v');
    var step :| NextStep(c, v, v', step);
    match step
      case ClientOpStep => {
        EqualMapsEqualKeysHeldUniquely(c, v, v');
        EqualMapsEqualMapp(c, v, v');
        var abistep :| TrustedABI.ClientOpStep(c.abi, v.abi, v'.abi, abistep);
        match abistep
          case AcceptRequestStep(request) => {
            assert MapSpec.NextStep(av, av', MapSpec.AcceptRequestStep(request)); // witness step
          }
          case DeliverReplyStep(request) => {
            assert MapSpec.NextStep(av, av', MapSpec.DeliverReplyStep(request)); // witness step
          }
      }
      case CommunicateStep(sendIdx, recvIdx, msg) => {
        TransferPreservesInvAndRefines(c, v, v', sendIdx, recvIdx, msg);
      }
      case LocalStep(hostIdx, abiOps) => {
        match abiOps.request
          case InsertRequest(_,_,_) => {
            InsertPreservesInvAndRefines(c, v, v', hostIdx, abiOps);
          }
          case QueryRequest(_,_) => {
            QueryPreservesInvAndRefines(c, v, v', hostIdx, abiOps);
          }
      }
//#end-elide
  }
}
