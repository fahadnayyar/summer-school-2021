//#title Synchronous KV Store
//#desc Build a refinement from a protocol (distributed sharded state) to
//#desc a specification (a logically-centralized abstract map).
//#desc TODO Conform to 2PC abstract proof obligation structure.

// "Synchronous" means network messages are delivered instantaneously -- we
// keep the challenge simpler here by pretending messages can be sent and
// delivered atomically.


include "../../library/Library.dfy"

module Types {
  // Rather than concretely explain the Key and Value types, we define the spec
  // and protocol over some uninterpreted types. The type declaration below says "there
  // is some type Key, but this protocol's behavior doesn't depend on what actual
  // type it is."

  // We need to tell Dafny two things about the type to convince it the type behaves
  // mathematically:
  // (==) means whatever this type is, it has equality defined on it.
  // !new means this type can't be allocated on the heap; it's a mathematical
  // immutable object.
  // Since we're in math-land, not implementation-land, we always want both features
  // of all types, so we declare them on these otherwise-unspecified types.
  // Missing == gives "map domain type must support equality" errors.
  // Missing !new gives "...not allowed to depend on the set of allocated
  // references" errors.
  type Key(==, !new)

  // Dafny's map<> type requires a finite domain. It also has an imap<> type that
  // allows an infinite domain, but we'd like to defer that complexity, so we'll stick
  // with finite maps.
  // Looking forward to the implementation, we can start with no keys stored, but we
  // are going to need to store "shard authority" information (which host is responsible
  // for each key) for every possible key, so eventually we're going to need to
  // have maps that contain every possible key. If we want to avoid imap<> for now,
  // then we'll need a finite keyspace. `type Key` is uninterpreted, and there's
  // no easy way to declare that it's finite.
  // (Side note: actually there is; Dafny has a predicate type constructor, but it's
  // flaky and sometimes crashes Dafny, so we're going to steer clear of it, too.)

  // So, just as we assume there's some space of Keys, let's assume a function that
  // defines a finite subset of those keys as the keyspace we're actually going to use.
  // We leave the function body absent, which means it's an axiom: we don't provide
  // the function, but assume such a function exists.
  // Everywhere we use a Key, we'll also require it to be in AllKeys().
  function AllKeys() : set<Key>

  type Value(==, !new)

  // To keep the API simple, we omit the concept of "the absence of a key", and instead
  // define a DefaultValue that keys have until Inserted otherwise.
  function DefaultValue() : Value
    // Again, No body -> this is an axiom.

  // This map comprehension assigns the DefaultValue to every key in the finite AllKeys()
  // keyspace. (Note that here the finite-ness of AllKeys() is now essential, as
  // it shows Dafny than the map has finite domain.)
  function InitialMap() : map<Key, Value>
  {
    map key | key in AllKeys() :: DefaultValue()
  }
}

// This module defines a Map state machine that serves as the system specification.
// You can tell by looking at this state machine that Key-Value pairs that get inserted
// are returned in Queries until otherwise inserted. It only talks about the semantics
// of Insert and Query; all of the details of a sharded implementation are left to
// the implementation.
module MapSpec {
  import opened Types

  datatype Variables = Variables(mapp:map<Key, Value>)

  predicate Init(v: Variables)
  {
    v.mapp == InitialMap()
    // Initially, every key maps to DefaultValue.
  }

  predicate InsertOp(v:Variables, v':Variables, key:Key, value:Value)
  {
    // A well-formed condition: we're not even gonna talk about keys other than AllKeys().
    && key in AllKeys()
    // Replace key with value. v.mapp domain remains AllKeys().
    && v'.mapp == v.mapp[key := value]
  }

  predicate QueryOp(v:Variables, v':Variables, key:Key, output:Value)
  {
    && key in AllKeys()
    // This is always true, but only visible by an inductive proof. We assume
    // it here so we can dereference v.mapp[key] on the next line. (If my claim
    // were wrong, then some Querys would be rejected by this test, which is a
    // liveness failure but not a safety failure.)
    && key in v.mapp
    && output == v.mapp[key]
    && v' == v  // no change to map state
  }

  datatype Step =
    | InsertOpStep(key:Key, value:Value)
    | QueryOpStep(key:Key, output:Value)
    | NoOpStep()

  predicate NextStep(v: Variables, v': Variables, step:Step)
  {
    match step
      case InsertOpStep(key, value) => InsertOp(v, v', key, value)
      case QueryOpStep(key, output) => QueryOp(v, v', key, output)
      case NoOpStep => v' == v
  }

  predicate Next(v: Variables, v': Variables)
  {
    exists step :: NextStep(v, v', step)
  }
}

module Implementation {
  import opened Library
  import opened Types

  type HostIdx = nat

  datatype Constants = Constants(mapCount: nat)
  {
    predicate WF() { 0 < mapCount }
    predicate ValidHost(idx: HostIdx) { idx < mapCount }
  }

  datatype Variables = Variables(maps:seq<map<Key, Value>>)
  {
    predicate WF(c: Constants) { |maps| == c.mapCount }
  }

  predicate Init(c: Constants, v: Variables)
  {
    && v.WF(c)
    && (forall idx:HostIdx | c.ValidHost(idx) :: v.maps[idx] == if idx==0 then InitialMap() else map[])
  }

  predicate Insert(c: Constants, v: Variables, v': Variables, idx: HostIdx, key: Key, value: Value)
  {
    && v.WF(c)
    && c.ValidHost(idx)
    && key in v.maps[idx] // the participating "host" needs to be authoritative on this key
    //&& key in AllKeys() // implied by previous conjunct + Inv()ariant
    && v'.maps == v.maps[idx := v.maps[idx][key := value]]
  }

  predicate Query(c: Constants, v: Variables, v': Variables, idx: HostIdx, key: Key, output: Value)
  {
    && v.WF(c)
    && c.ValidHost(idx)
    && key in v.maps[idx] // the participating "host" needs to be authoritative on this key
    && output == v.maps[idx][key]
    && v' == v  // UNCHANGED
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
    && v'.maps[sendIdx] == MapRemoveOne(v.maps[sendIdx], key)  // key leaves sending map
    && v'.maps[recvIdx] == v.maps[recvIdx][key := value]    // key appears in recv map
    && (forall otherIdx:HostIdx | c.ValidHost(otherIdx) && otherIdx != sendIdx && otherIdx != recvIdx
        :: v'.maps[otherIdx] == v.maps[otherIdx]) // unchanged other participants
  }

  datatype Step =
    | InsertStep(idx: HostIdx, key: Key, value: Value)
    | QueryStep(idx: HostIdx, key: Key, output: Value)
    | TransferStep(sendIdx: HostIdx, recvIdx: HostIdx, key: Key, value: Value)

  predicate NextStep(c: Constants, v: Variables, v': Variables, step: Step)
  {
    match step
      case InsertStep(idx, key, value) => Insert(c, v, v', idx, key, value)
      case QueryStep(idx, key, output) => Query(c, v, v', idx, key, output)
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
  import opened Implementation

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
    requires exists hostidx :: HostHasKey(c, v, hostidx, key);
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
    MapSpec.Variables(map key | key in KnownKeys(c, v) :: AbstractionOneKey(c, v, key))
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
  lemma InitRefines(c: Constants, v: Variables)
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


  lemma InsertPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, insertHost: HostIdx, insertedKey: Key, value: Value)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(insertHost)
    requires Insert(c, v, v', insertHost, insertedKey, value)
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
//#start-elide
    var abstractMap := Abstraction(c, v).mapp;
    var abstractMap' := Abstraction(c, v').mapp;

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
    assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.InsertOpStep(insertedKey, value)); // witness
//#end-elide
  }

  lemma QueryPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, queryHost: HostIdx, key: Key, output: Value)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(queryHost)
    requires Query(c, v, v', queryHost, key, output)
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
//#start-elide
    assert v == v'; // weirdly obvious trigger
    assert Inv(c, v') by { reveal_KeysHeldUniquely(); }
    assert key in KnownKeys(c, v) by { HostKeysSubsetOfKnownKeys(c, v, c.mapCount); }
    assert output == Abstraction(c, v).mapp[key] by {
      assert HostHasKey(c, v, queryHost, key);  // witness
      reveal_KeysHeldUniquely();
    }
    assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.QueryOpStep(key, output)); // witness
//#end-elide
  }

  lemma TransferPreservesInvAndRefines(c: Constants, v: Variables, v': Variables, sendIdx: HostIdx, recvIdx: HostIdx, sentKey: Key, value: Value)
    requires Inv(c, v)
    requires Next(c, v, v')
    requires c.ValidHost(sendIdx)
    requires c.ValidHost(recvIdx)
    requires Transfer(c, v, v', sendIdx, recvIdx, sentKey, value)
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
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
    assert MapSpec.NextStep(Abstraction(c, v), Abstraction(c, v'), MapSpec.NoOpStep); // witness
//#end-elide
  }

  lemma NextPreservesInvAndRefines(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
    ensures MapSpec.Next(Abstraction(c, v), Abstraction(c, v'))
  {
//#start-elide
    var step :| NextStep(c, v, v', step);
    match step
      case InsertStep(idx, key, value) => {
        InsertPreservesInvAndRefines(c, v, v', idx, key, value);
      }
      case QueryStep(idx, key, output) => {
        QueryPreservesInvAndRefines(c, v, v', idx, key, output);
      }
      case TransferStep(sendIdx, recvIdx, key, value) => {
        TransferPreservesInvAndRefines(c, v, v', sendIdx, recvIdx, key, value);
      }
//#end-elide
  }
}