//#title Application Correspondence with Synchronous Sharded KV Store
//#desc How do we prevent a nonsense refinement theorem, for example one that does whatever
//#desc it wants, but abstracts every protocol-level state to the initial spec state, so it
//#desc can refine to a bunch of stutter steps?

include "../../chapter07-async-clients/solutions/exercise01_solution.dfy" //#magicinline

// For reference, go see your or the instructors' solution to chapter06-refine/exercises/exercise01.dfy
module AsyncClientShardedKVProtocol {
  import opened Library
  import opened Types

  type HostIdx = nat

  datatype Constants = Constants(mapCount: nat)
  {
    predicate WF() { 0 < mapCount }
    predicate ValidHost(idx: HostIdx) { idx < mapCount }
  }

  datatype Variables = Variables(maps:seq<map<Key, Value>>, requests:set<Input>, replies:set<Output>)
  {
    predicate WF(c: Constants) {
      && c.WF()
      && |maps| == c.mapCount
    }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall idx:HostIdx | c.ValidHost(idx) :: v.maps[idx] == if idx==0 then InitialMap() else map[])
    && v.requests == {}
    && v.replies == {}
  }
  predicate AcceptRequest(v:Variables, v':Variables, request: Input)
  {
//#exercise    false // TODO Define this predicate
//#start-elide
    && request !in v.requests // (liveness only) if client picked identical nonces, don't let the requests collapse.
    && v' == v.(requests := v.requests + {request})
//#end-elide
  }

  predicate DeliverReply(v:Variables, v':Variables, reply: Output)
  {
//#exercise    false // TODO Define this predicate
//#start-elide
    && reply in v.replies
    && v' == v.(replies := v.replies - {reply})
//#end-elide
  }

  predicate Insert(c: Constants, v: Variables, v': Variables, idx: HostIdx, request: Input)
  {
    && v.WF(c)
    && c.ValidHost(idx)
    && request in v.requests
    && request.InsertRequest?
    && var reply := InsertReply(request);
    && reply !in v.replies
    && request.key in v.maps[idx] // the participating "host" needs to be authoritative on this key
    //&& key in AllKeys() // implied by previous conjunct + Inv()ariant
    && v' == v.(
      maps := v.maps[idx := v.maps[idx][request.key := request.value]],
      requests := v.requests - {request},
      replies := v.replies + {reply})
              
  }

  predicate Query(c: Constants, v: Variables, v': Variables, idx: HostIdx, request: Input, output: Value)
  {
    && v.WF(c)
    && c.ValidHost(idx)
    && request in v.requests
    && request.QueryRequest?
    && var reply := QueryReply(request, output);
    && reply !in v.replies
    && request.key in v.maps[idx] // the participating "host" needs to be authoritative on this key
    && output == v.maps[idx][request.key]
    && v' == v.(
      requests := v.requests - {request},
      replies := v.replies + {reply})
  }

  // A possible enhancement exercise: transfer many key,value pairs in one step
  predicate Transfer(c: Constants, v: Variables, v': Variables, sendIdx: HostIdx, recvIdx: HostIdx, key: Key, value: Value)
  {
    && v.WF(c)
    && v'.WF(c)
    && c.ValidHost(sendIdx)
    && c.ValidHost(recvIdx)
    && key in v.maps[sendIdx]
    && v.maps[sendIdx][key] == value
    && v' == v.(
      maps := v.maps[sendIdx := MapRemoveOne(v.maps[sendIdx], key)]  // key leaves sending map
                    [recvIdx := v.maps[recvIdx][key := value]]       // key appears in recv map
         // ... no changes to application-visible requests, replies
      )
  }

  datatype Step =
    | AcceptRequestStep(request:Input)
    | DeliverReplyStep(reply: Output)
    | InsertStep(idx: HostIdx, request: Input)
    | QueryStep(idx: HostIdx, request: Input, output: Value)
    | TransferStep(sendIdx: HostIdx, recvIdx: HostIdx, key: Key, value: Value)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    match step
      case AcceptRequestStep(request) => AcceptRequest(v, v', request)
      case DeliverReplyStep(request) => DeliverReply(v, v', request)
    
      case InsertStep(idx, request) => Insert(c, v, v', idx, request)
      case QueryStep(idx, request, output) => Query(c, v, v', idx, request, output)
      case TransferStep(sendIdx, recvIdx, key, value) => Transfer(c, v, v', sendIdx, recvIdx, key, value)
  }

  predicate Next(c: Constants, v: Variables, v': Variables)
  {
    exists step :: NextStep(c, v, v', step)
  }
}

module RefinementProof {
  import opened Library
  import opened Types
  import MapSpec
  import opened AsyncClientShardedKVProtocol

  predicate HostHasKey(c: Constants, v: Variables, hostidx:HostIdx, key:Key)
    requires v.WF(c)
  {
    && c.ValidHost(hostidx)
    && key in v.maps[hostidx]
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
      v.maps[KeyHolder(c, v, key)][key]
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
    seq(c.mapCount, i requires 0<=i<c.mapCount => v.maps[i].Keys)
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
    requires count <= c.mapCount
    ensures forall idx | 0 <= idx < count :: v.maps[idx].Keys <= KnownKeys(c, v)
  {
    forall idx | 0 <= idx < count ensures v.maps[idx].Keys <= KnownKeys(c, v)
    {
      SetsAreSubsetsOfUnion(MapDomains(c, v));
      assert v.maps[idx].Keys == MapDomains(c, v)[idx];  // trigger
    }
  }

  function Abstraction(c: Constants, v: Variables) : MapSpec.Variables
    requires v.WF(c)
  {
//#exercise    MapSpec.Variables(InitialMap()) // Replace me
//#start-elide
    MapSpec.Variables(
      map key | key in KnownKeys(c, v) :: AbstractionOneKey(c, v, key),
      v.requests,
      v.replies)
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
          && key in v.maps[hostidx] && key in v.maps[otherhost]
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
    requires 0 < count <= c.mapCount
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
    InitAllKeysEmpty(c, v, c.mapCount);
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
  lemma InsertPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, insertHost: HostIdx, request:Input)
      returns (specstep: MapSpec.Step)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(insertHost)
    requires Insert(c, v, v', insertHost, request)
    ensures Inv(c, v')
    ensures MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), specstep)
  {
//#start-elide
    var abstractMap := Abstraction(c, v).mapp;
    var abstractMap' := Abstraction(c, v').mapp;
    var insertedKey := request.key; // use some let-in assignments to recycle chapter06 proof...
    var value := request.value;

    assert insertedKey in AllKeys() by {
      SetsAreSubsetsOfUnion(MapDomains(c, v));
      assert MapDomains(c, v)[insertHost] == v.maps[insertHost].Keys; //trigger
    }

    assert KeysHeldUniquely(c, v') by { reveal_KeysHeldUniquely(); }

    forall key
      ensures key in abstractMap' <==> key in abstractMap || key == insertedKey // domain
      ensures key in abstractMap' ==> (abstractMap'[key] == if key==insertedKey then value else abstractMap[key])  // value
    {
      if key == insertedKey {
        SetsAreSubsetsOfUnion(MapDomains(c, v'));
        assert MapDomains(c, v')[insertHost] <= KnownKeys(c, v'); // trigger
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
          AnyHostWithKeyIsKeyHolder(c, v', insertHost, key);
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
    specstep := MapSpec.InsertOpStep(request);  // what used to be a witness is now explicitly exposed.
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
    var idx :| 0<=idx<c.mapCount && key in MapDomains(c, v)[idx];
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
    requires v'.maps == v.maps
    ensures KeysHeldUniquely(c, v') == KeysHeldUniquely(c, v)
  {
    reveal_KeysHeldUniquely();
  }

  lemma EqualMapsEqualMapp(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Inv(c, v')
    requires v'.maps == v.maps
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
  lemma QueryPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, queryHost: HostIdx, request: Input, output: Value) returns (specstep: MapSpec.Step)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(queryHost)
    requires Query(c, v, v', queryHost, request, output)
    ensures Inv(c, v')
    ensures MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), specstep)
  {
//#start-elide
    var key := request.key;
    assert v.maps == v'.maps; // weirdly obvious trigger
    assert Inv(c, v') by { reveal_KeysHeldUniquely(); }
    assert key in KnownKeys(c, v) by { HostKeysSubsetOfKnownKeys(c, v, c.mapCount); }
    assert output == Abstraction(c, v).mapp[key] by {
      assert HostHasKey(c, v, queryHost, key);  // witness
      reveal_KeysHeldUniquely();
    }
    EqualMapsEqualMapp(c, v, v');
    specstep := MapSpec.QueryOpStep(request, output);  // what used to be a witness is now explicitly exposed.
//#end-elide
  }

  // This is not a goal by itself, it's one of the cases you'll need to prove
  // NextPreservesInvAndRefines. We've provided its signature to help you
  // structure your overall proof.
  lemma TransferPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, sendIdx: HostIdx, recvIdx: HostIdx, sentKey: Key, value: Value) returns (specstep: MapSpec.Step)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(sendIdx)
    requires c.ValidHost(recvIdx)
    requires Transfer(c, v, v', sendIdx, recvIdx, sentKey, value)
    ensures Inv(c, v')
    ensures MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), specstep)
  {
//#start-elide
    // domain preserved
    forall key
      ensures key in Abstraction(c, v).mapp <==> key in Abstraction(c, v').mapp
    {
      var idx;
      if key in Abstraction(c, v).mapp {
        SetsAreSubsetsOfUnion(MapDomains(c, v'));
        if key==sentKey {
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
        if key==sentKey {
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
      if key == sentKey {
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
    specstep := MapSpec.NoOpStep; // what used to be a witness is now explicitly exposed.
//#end-elide
  }

  // This trusted predicate forces application-visible actions to keep the same labels.
  predicate RefinementHonorsApplicationCorrespondence(c: Constants, v: Variables, v': Variables, step: Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
  {
    // Application-visible steps are labeled as such in the spec action
    && (step.AcceptRequestStep?
        ==> MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.AcceptRequestStep(step.request)))
    && (step.DeliverReplyStep?
        ==> MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.DeliverReplyStep(step.reply)))
    // If protocol step isn't application-visible...
    && (!step.AcceptRequestStep? && !step.DeliverReplyStep? ==>
        // then whatever happened in the spec wasn't an application-visible step.
        forall specstep:MapSpec.Step | specstep.AcceptRequestStep? || specstep.DeliverReplyStep?
          :: !MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), specstep))
  }

  // The proof goal is modified from chapter06 to expose the protocl- and
  // spec-level step objects so we can add an application-correspendence check
  // as an ensures. So where we used to just producte a witness to the application-level
  // step, we now have to actually return it to satisfy the lemmas' mentions of NextStep
  // (instead of just Next).
  lemma RefinementNext(c: Constants, v: Variables, v': Variables, step: Step) returns (specstep: MapSpec.Step)
    requires Inv(c, v)
    requires NextStep(c, v, v', step)
    ensures Inv(c, v')
    ensures MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), specstep)
    ensures RefinementHonorsApplicationCorrespondence(c, v, v', step) // demand proof of application correspondence
  {
    // Use InsertPreservesInvAndRefines, QueryPreservesInvAndRefines, and
    // TransferPreservesInvAndRefines here to complete this proof.
//#start-elide
    var step :| NextStep(c, v, v', step);
    match step
      case AcceptRequestStep(request) => {
        EqualMapsEqualKeysHeldUniquely(c, v, v');
        EqualMapsEqualMapp(c, v, v');
        specstep := MapSpec.AcceptRequestStep(request);
      }
      case DeliverReplyStep(request) => {
        EqualMapsEqualKeysHeldUniquely(c, v, v');
        EqualMapsEqualMapp(c, v, v');
        specstep := MapSpec.DeliverReplyStep(request);
      }
      case InsertStep(idx, request) => {
        specstep := InsertPreservesInvAndRefines(c, v, v', idx, request);
      }
      case QueryStep(idx, request, output) => {
        specstep := QueryPreservesInvAndRefines(c, v, v', idx, request, output);
      }
      case TransferStep(sendIdx, recvIdx, key, value) => {
        specstep := TransferPreservesInvAndRefines(c, v, v', sendIdx, recvIdx, key, value);
      }
//#end-elide
  }
}
