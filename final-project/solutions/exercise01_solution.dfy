//#title Final Project
//#desc Design a Sharded Hash Table (SHT) protocol and prove it is correct.

// XXX TODO right now we don't give students ANYTHING about the trusted framework.
// That feels like too little -- we're not trying to teach people to construct new
// trusted frameworks, since the same basic framework can be reused in many settings.

// The SHT should consist of a number of nodes storing key-value pairs.
// There are no external clients; the nodes perform Get()'s and Put()'s on the keys directly.
// A node can only perform a Get or Put on a key it owns.
// Each key is owned by exactly one node.
// A node can transfer ownership of a set of keys (a.k.a. shard) to another node by sending it a TransferMessage that is delivered asynchronously (i.e. as part of a different state transition)
// All actions should be defined at the protocol level (i.e. as predicates) and not as imperative methods.
//
// The entire application should behave like a logically centralized hash table.

// You should assume that the network delivers packets at-most-once so you don't
// have to deal with the duplicate-defeating epoch number mechanism from
// the midterm (chapter06) exercise. hints/hint00 provides the necessary
// changes to network.s.dfy file, if you are uncomfortable trying to make that
// change yourself.

// Here are some handy library functions that you may find useful for
// manipulating maps.
//
// You may recall that, in some lecture examples, we
// refined a hash table to a map, and then a sharded hash table to a map.
// Your protocol doesn't NOT need to build a linear-probing hash table --
// the local state on each Host may be a Dafny map<>.

module Base {
  function ZeroMap() : imap<int,int>
  {
    imap i | true :: 0
  }

  function EmptyMap() : imap<int,int>
  {
    imap i | false :: 0
  }

  function MapUnionPreferLeft<K(!new),V>(a:map<K,V>, b:map<K,V>) : map<K,V>
  {
    map key | key in a.Keys + b.Keys :: if key in a then a[key] else b[key]
  }

  function IMapUnionPreferLeft(a:imap<int,int>, b:imap<int,int>) : imap<int,int>
  {
    imap key | key in a || key in b :: if key in a then a[key] else b[key]
  }

  function {:opaque} MapRemoveOne<K,V>(m:map<K,V>, key:K) : (m':map<K,V>)
    ensures forall k :: k in m && k != key ==> k in m'
    ensures forall k :: k in m' ==> k in m && k != key
    ensures forall j :: j in m' ==> m'[j] == m[j]
    ensures |m'.Keys| <= |m.Keys|
    ensures |m'| <= |m|
  {
    var m':= map j | j in m && j != key :: m[j];
    assert m'.Keys == m.Keys - {key};
    m'
  }

  function MapRemove(table:imap<int,int>, removeKeys:iset<int>) : imap<int,int>
    requires removeKeys <= table.Keys
  {
    imap key | key in table && key !in removeKeys :: table[key]
  }

}

//#start-elide
//////////////////////////////////////////////////////////////////////////////
// Application spec

module HashTable {
  import opened Base

  predicate {:opaque} IsFull(m:imap<int, int>) {
    forall i :: i in m
  }
  function FullMapWitness() : (m:imap<int,int>)
    ensures IsFull(m)
  {
    reveal_IsFull();
    imap key:int | true :: 0
  }
  type FullMap = m: imap<int, int> | IsFull(m)
    ghost witness FullMapWitness()

  datatype Constants = Constants()
  datatype Variables = Variables(table:FullMap)
  
  predicate Init(constants:Constants, state:Variables) {
    state.table == ZeroMap()
  }

  predicate Get(constants:Constants, state:Variables, state':Variables, key:int, value:int) {
    && state.table[key] == value
    && state' == state
  }

  predicate Put(constants:Constants, state:Variables, state':Variables, key:int, value:int) {
    && state'.table == state.table[key := value]
  }

  datatype Step = GetStep(key:int, value:int) | PutStep(key:int, value:int)

  predicate NextStep(constants:Constants, state:Variables, state':Variables, step:Step) {
    match step {
      case GetStep(key, value) => Get(constants, state, state', key, value)
      case PutStep(key, value) => Put(constants, state, state', key, value)
    }
  }

  predicate Next(constants:Constants, state:Variables, state':Variables) {
    exists step :: NextStep(constants, state, state', step)
  }
}

//////////////////////////////////////////////////////////////////////////////
// Environment spec

module Environment {
  function NumHosts() : nat
    ensures NumHosts() > 0

  newtype HostId = b: int | 0 <= b < NumHosts()
  function AllHosts() : set<HostId> {
    set h:HostId | true
  }
  datatype Option<V> = None | Some(value:V)
  datatype NetAction<M> = NetAction(rcv:Option<M>, send:set<M>)
}

module Network {
  import opened Environment

  datatype Constants = Constants()
  datatype Variables<M> = Variables(messageSet:set<M>)

  predicate Init(constants:Constants, state:Variables) {
    state.messageSet == {}
  }

  predicate Next(constants:Constants, state:Variables, state':Variables, a:NetAction) {
    && (a.rcv.Some? ==> a.rcv.value in state.messageSet)
    && state'.messageSet == state.messageSet
      - ( if a.rcv.Some? then {a.rcv.value} else {} )
      + a.send
  }
}

abstract module DistributedSystem {
  import opened Environment
  import Network

  // parameters filled in by refining module
  type M(!new,==)
  type HConstants
  type HVariables
  type HStep(!new,==)
  predicate HInit(constants:HConstants, state:HVariables, id:HostId)
  predicate HNextStep(constants:HConstants, state:HVariables, state':HVariables, a:NetAction<M>, step:HStep)

  type HostMap<V> = m:map<HostId, V> | m.Keys == AllHosts()
    ghost witness var v:V :| true; map h:HostId | h in AllHosts() :: v
  type HostConstantsMap = HostMap<HConstants>
  type HostVariablesMap = HostMap<HVariables>
  datatype Constants
    = Constants(hosts:HostConstantsMap, network:Network.Constants)
  datatype Variables
    = Variables(hosts:HostVariablesMap, network:Network.Variables<M>)
  
  predicate Init(constants:Constants, state:Variables) {
    && (forall id :: HInit(constants.hosts[id], state.hosts[id], id))
    && Network.Init(constants.network, state.network)
  }

  predicate NextStep(constants:Constants, state:Variables, state':Variables, id:HostId, a:NetAction<M>, step:HStep) {
    && HNextStep(constants.hosts[id], state.hosts[id], state'.hosts[id], a, step)
    && (forall other :: other != id ==> state'.hosts[other] == state.hosts[other])
    && Network.Next(constants.network, state.network, state'.network, a)
  }

  predicate Next(constants:Constants, state:Variables, state':Variables) {
    exists id, a, step :: NextStep(constants, state, state', id, a, step)
  }
}

//////////////////////////////////////////////////////////////////////////////
// Protocol

module Host {
  import opened Base
  import opened Environment

  datatype Message = Transfer(table:imap<int,int>)

  datatype Constants = Constants(id:HostId)
  datatype Variables = Variables(table:imap<int,int>)

  predicate Get(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>, key:int, value:int) {
    && key in state.table
    && state.table[key] == value
    && state' == state
    && a.rcv.None?
    && a.send == {}
  }

  predicate Put(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>, key:int, value:int) {
    && key in state.table
    && state'.table == state.table[key := value]
    && a.rcv.None?
    && a.send == {}
  }

  predicate SendShard(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>, m:Message) {
    && a.rcv.None?
    && a.send == {m}
    && m.table.Keys <= state.table.Keys
    && (forall key :: key in m.table ==> m.table[key] == state.table[key])
    && state'.table == MapRemove(state.table, m.table.Keys)
  }

  predicate ReceiveShard(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>) {
    && a.rcv.Some?
    && a.send == {}
    && var m := a.rcv.value;
    && state'.table == IMapUnionPreferLeft(state.table, m.table)
  }

  predicate Init(constants:Constants, state:Variables, id:HostId) {
    state.table == if id == 0 then ZeroMap() else EmptyMap()
  }

  datatype Step =
    | GetStep(key:int, value:int)
    | PutStep(key:int, value:int)
    | SendShardStep(m:Message)
    | ReceiveShardStep()

  predicate NextStep(constants:Constants, state:Variables, state':Variables, a:NetAction<Message>, step:Step) {
    match step {
      case GetStep(key, value) => Get(constants, state, state', a, key, value)
      case PutStep(key, value) => Put(constants, state, state', a, key, value)
      case SendShardStep(m) => SendShard(constants, state, state', a, m)
      case ReceiveShardStep() => ReceiveShard(constants, state, state', a)
    }
  }
}

module ShardedHashTable refines DistributedSystem {
  import Host

  type M = Host.Message
  type HConstants = Host.Constants
  type HVariables = Host.Variables
  type HStep(!new,==) = Host.Step

  predicate HInit(constants:HConstants, state:HVariables, id:HostId) {
    Host.Init(constants, state, id)
  }

  predicate HNextStep(constants:HConstants, state:HVariables, state':HVariables, a:NetAction<M>, step:HStep) {
    Host.NextStep(constants, state, state', a, step)
  }
}

//////////////////////////////////////////////////////////////////////////////
// Proof

abstract module RefinementTheorem {
  import HashTable
  import opened Environment
  import opened ShardedHashTable

  function Ik(constants:Constants) : HashTable.Constants
  function I(constants:Constants, state:Variables) : HashTable.Variables
  predicate Inv(constants:Constants, state:Variables)

  lemma RefinementInit(constants:Constants, state:Variables)
    requires Init(constants, state)
    ensures Inv(constants, state) // Inv base case
    ensures HashTable.Init(Ik(constants), I(constants, state))  // Refinement base case

  lemma RefinementNext(constants:Constants, state:Variables, state':Variables)
    requires Next(constants, state, state')
    requires Inv(constants, state)
    ensures Inv(constants, state')  // Inv inductive step
    ensures HashTable.Next(Ik(constants), I(constants, state), I(constants, state'))
        || I(constants, state) == I(constants, state') // Refinement inductive step
}

module RefinementProof refines RefinementTheorem {
  import opened Base

  function Ik(constants:Constants) : HashTable.Constants
  {
    HashTable.Constants()
  }

  datatype MapOwner = HostOwner(id:HostId) | MessageOwner(msg:Host.Message)
  type MapGathering = map<MapOwner,imap<int,int>>

  predicate MapsAreDisjoint(maps:MapGathering)
  {
    forall src1, src2 :: src1 in maps && src2 in maps && src1 != src2 ==> maps[src1].Keys !! maps[src2].Keys
  }

  // forall-exists puts Dafny in a bad mood
  predicate {:opaque} MapsAreFull(maps:MapGathering)
  {
    forall key :: exists src :: src in maps && key in maps[src]
  }

  predicate MapsPartitionFullMap(maps:MapGathering)
  {
    && MapsAreDisjoint(maps)
    && MapsAreFull(maps)
  }

  function HostMaps(constants:Constants, state:Variables) : (hm:MapGathering)
  {
    var sourceSet := set i | true :: HostOwner(i);
    map src | src in sourceSet :: state.hosts[src.id].table
  }

  function TransferMaps(constants:Constants, state:Variables) : MapGathering
  {
    var sourceSet := set m | m in state.network.messageSet :: MessageOwner(m);
    map src | src in sourceSet :: src.msg.table
  }

  function LiveMaps(constants:Constants, state:Variables) : MapGathering
  {
    MapUnionPreferLeft(HostMaps(constants, state), TransferMaps(constants, state))
  }

  // Dafny'state :| should be deterministic (functional), but it ain't.
  function TheOwnerYouChoose(maps:MapGathering) : MapOwner
    requires maps != map[]
  {
    var source :| source in maps; source
  }

  function DisjointMapUnion(maps:MapGathering) : imap<int,int>
  {
    if maps == map[]
    then EmptyMap()
    else
      var source := TheOwnerYouChoose(maps);
      IMapUnionPreferLeft(DisjointMapUnion(MapRemoveOne(maps, source)), maps[source])
  }

  function ForceFilled(m:imap<int,int>) : HashTable.FullMap
  {
    if HashTable.IsFull(m) then m else ZeroMap()
  }

  function I(constants:Constants, state:Variables) : HashTable.Variables
  {
    HashTable.Variables(ForceFilled(DisjointMapUnion(LiveMaps(constants, state))))
  }

  predicate Inv(constants:Constants, state:Variables) {
    MapsPartitionFullMap(LiveMaps(constants, state))
  }

  lemma GatheringOfEmptyMaps(mg:MapGathering)
    requires forall src :: src in mg ==> mg[src] == EmptyMap()
    ensures DisjointMapUnion(mg) == EmptyMap()
  {
  }

  lemma EmptyMapsDontMatter(mg:MapGathering, vsrc:MapOwner)
    requires vsrc in mg.Keys
    requires forall src :: src in mg && src != vsrc ==> mg[src] == EmptyMap()
    ensures DisjointMapUnion(mg) == mg[vsrc]
  {
    if mg.Keys != {vsrc} {
      var csource := TheOwnerYouChoose(mg);
      if csource == vsrc {
        GatheringOfEmptyMaps(MapRemoveOne(mg, csource));
      } else {
        EmptyMapsDontMatter(MapRemoveOne(mg, csource), vsrc);
      }
    }
  }

  lemma RefinementInit(constants:Constants, state:Variables)
    //requires Init(constants, state) // inherited from abstract module
    ensures Inv(constants, state)
    ensures HashTable.Init(Ik(constants), I(constants, state))
  {
    assert LiveMaps(constants, state)[HostOwner(0)] == ZeroMap();  // TRIGGER
    EmptyMapsDontMatter(LiveMaps(constants, state), HostOwner(0));
    reveal_MapsAreFull();
  }

  // Controlled revelation: access a little bit of MapsAreFull definition without getting trigger-crazy.
  function {:opaque} UseMapsAreFull(maps:MapGathering, key:int) : (src:MapOwner)
    requires MapsAreFull(maps)
    ensures src in maps && key in maps[src]
  {
    reveal_MapsAreFull();
    var src :| src in maps && key in maps[src];
    src
  }

  lemma PutKeepsMapsFull(constants:Constants, state:Variables, state':Variables, id:HostId, a:NetAction<M>, key:int, value:int)
    requires Inv(constants, state)
    requires NextStep(constants, state, state', id, a, Host.PutStep(key, value))
    ensures MapsAreFull(LiveMaps(constants, state'))
  {
    var maps := LiveMaps(constants, state);
    var maps' := LiveMaps(constants, state');
    forall key
      ensures exists src' :: src' in maps' && key in maps'[src']
    {
      var src := UseMapsAreFull(maps, key);
      assert src in maps' && key in maps'[src];
    }
    reveal_MapsAreFull();
  }

  lemma SendShardKeepsMapsFull(constants:Constants, state:Variables, state':Variables, id:HostId, a:NetAction<M>, msg:Host.Message)
    requires Inv(constants, state)
    requires NextStep(constants, state, state', id, a, Host.SendShardStep(msg))
    ensures MapsAreFull(LiveMaps(constants, state'))
  {
    var maps := LiveMaps(constants, state);
    var maps' := LiveMaps(constants, state');
    forall key
      ensures exists src' :: src' in maps' && key in maps'[src']
    {
      var src := if key in msg.table then MessageOwner(msg) else UseMapsAreFull(maps, key);
      assert src in maps' && key in maps'[src];
    }
    reveal_MapsAreFull();
  }

  lemma ReceiveShardKeepsMapsFull(constants:Constants, state:Variables, state':Variables, id:HostId, a:NetAction<M>)
    requires Inv(constants, state)
    requires NextStep(constants, state, state', id, a, Host.ReceiveShardStep())
    ensures MapsAreFull(LiveMaps(constants, state'))
  {
    var maps := LiveMaps(constants, state);
    var maps' := LiveMaps(constants, state');
    forall key
      ensures exists src' :: src' in maps' && key in maps'[src']
    {
      var oldSrc := UseMapsAreFull(maps, key);
      var src := if oldSrc == MessageOwner(a.rcv.value) then HostOwner(id) else oldSrc;
      assert src in maps' && key in maps'[src];
    }
    reveal_MapsAreFull();
  }

  lemma DisjointMapsDontContainKey(maps:MapGathering, key:int)
    requires forall src :: src in maps ==> key !in maps[src]
    ensures key !in DisjointMapUnion(maps)
  {
  }

  lemma DisjointMapsMapKeyToValue(maps:MapGathering, src:MapOwner, key:int)
    requires MapsAreDisjoint(maps)
    requires src in maps
    requires key in maps[src]
    ensures key in DisjointMapUnion(maps)
    ensures DisjointMapUnion(maps)[key] == maps[src][key]
  {
    if maps.Keys != {src} {
      var rSrc := TheOwnerYouChoose(maps);
      if src == rSrc {
        DisjointMapsDontContainKey(MapRemoveOne(maps, rSrc), key);
        assert key !in DisjointMapUnion(MapRemoveOne(maps, rSrc));
      } else {
        DisjointMapsMapKeyToValue(MapRemoveOne(maps, rSrc), src, key);
      }
    }
  }

  lemma MapsPartitionImpliesIsFull(maps:MapGathering)
    requires MapsPartitionFullMap(maps)
    ensures HashTable.IsFull(DisjointMapUnion(maps))
  {
    HashTable.reveal_IsFull();
    forall key ensures key in DisjointMapUnion(maps)
    {
      var src := UseMapsAreFull(maps, key);
      DisjointMapsMapKeyToValue(maps, src, key);
    }
  }

  lemma RefinementNext(constants:Constants, state:Variables, state':Variables)
    // requires Next(constants, state, state')
    // requires Inv(constants, state)
    ensures Inv(constants, state')  // Inv inductive step
  {
    var maps := LiveMaps(constants, state);
    var maps' := LiveMaps(constants, state');
    var id, a, step :| ShardedHashTable.NextStep(constants, state, state', id, a, step);
    var hostconstants := constants.hosts[id];
    var hoststate := state.hosts[id];
    var hoststate' := state'.hosts[id];
    match step {
      case GetStep(key, value) => {
        assert state == state';
        DisjointMapsMapKeyToValue(maps, HostOwner(id), key);
        MapsPartitionImpliesIsFull(maps);
      }
      case PutStep(key, value) => {
        forall src1, src2 | src1 in maps' && src2 in maps' && src1 != src2
        ensures maps'[src1].Keys !! maps'[src2].Keys
        {
          var oldMap := state.hosts[id].table;
          if src1 == HostOwner(id) {
            assert maps[src1] == oldMap;  // TRIGGER disjointness hypothesis
            assert maps[src2] == maps'[src2];
          } else if src2 == HostOwner(id) {
            assert maps[src1] == maps'[src1];
            assert maps[src2] == oldMap;
          } else {
            assert maps[src1] == maps'[src1];
            assert maps[src2] == maps'[src2];
          }
        }
        PutKeepsMapsFull(constants, state, state', id, a, key, value);
        MapsPartitionImpliesIsFull(maps);
        MapsPartitionImpliesIsFull(maps');
        forall kk
          ensures I(constants, state').table[kk] == I(constants, state).table[key := value][kk]
        {
          if kk == key {
            DisjointMapsMapKeyToValue(maps', HostOwner(id), key);
          } else {
            var src := UseMapsAreFull(maps, kk);
            var src' := UseMapsAreFull(maps', kk);
            DisjointMapsMapKeyToValue(maps, src, kk);
            DisjointMapsMapKeyToValue(maps', src', kk);
            if src == HostOwner(id) {
              if src' != HostOwner(id) {
                assert maps[src'] == maps'[src'];
                assert false;
              }
            } else {
              if src' != src {
                assert maps[src'] == maps'[src'];
                assert false;
              }
            }
          }
        }
        assert HashTable.NextStep(Ik(constants), I(constants, state), I(constants, state'), HashTable.PutStep(key, value)); // trigger
      }
      case SendShardStep(msg) => {
        forall src1, src2 | src1 in maps' && src2 in maps' && src1 != src2
        ensures maps'[src1].Keys !! maps'[src2].Keys
        {
          if src1 == HostOwner(id) {
            assert maps'[src1].Keys <= maps[src1].Keys;
          } else if src1 == MessageOwner(msg) {
            assert maps'[src1].Keys <= maps[HostOwner(id)].Keys;
          } else {
            assert maps'[src1].Keys == maps[src1].Keys; // trigger
          }
          if src2 == HostOwner(id) {
            assert maps'[src2].Keys <= maps[src2].Keys;
          } else if src2 == MessageOwner(msg) {
            assert maps'[src2].Keys <= maps[HostOwner(id)].Keys;
          } else {
            assert maps'[src2].Keys == maps[src2].Keys; // trigger
          }
        }
        SendShardKeepsMapsFull(constants, state, state', id, a, msg);
        MapsPartitionImpliesIsFull(maps);
        MapsPartitionImpliesIsFull(maps');
        forall kk
          ensures I(constants, state').table[kk] == I(constants, state).table[kk]
        {
          var src := UseMapsAreFull(maps, kk);
          var src' := UseMapsAreFull(maps', kk);
          DisjointMapsMapKeyToValue(maps, src, kk);
          DisjointMapsMapKeyToValue(maps', src', kk);
          if src' == MessageOwner(msg) {
            if src != HostOwner(id) {
              assert kk in maps[HostOwner(id)];
              assert false;
            }
          } else {
            if src != src' {
              assert kk in maps[src'];
              assert false;
            }
          }
        }
      }
      case ReceiveShardStep() => {
        var msg := a.rcv.value;
        forall src1, src2 | src1 in maps' && src2 in maps' && src1 != src2
        ensures maps'[src1].Keys !! maps'[src2].Keys
        {
          if src1 == HostOwner(id) {
            assert maps[src1].Keys <= maps'[src1].Keys;
            assert maps[MessageOwner(msg)].Keys <= maps'[src1].Keys;
          } else {
            assert maps'[src1].Keys == maps[src1].Keys; // trigger
          }
          if src2 == HostOwner(id) {
            assert maps[src2].Keys <= maps'[src2].Keys;
            assert maps[MessageOwner(msg)].Keys <= maps'[src2].Keys;
          } else {
            assert maps'[src2].Keys == maps[src2].Keys; // trigger
          }
        }
        ReceiveShardKeepsMapsFull(constants, state, state', id, a);
        MapsPartitionImpliesIsFull(maps);
        MapsPartitionImpliesIsFull(maps');
        forall kk
          ensures I(constants, state').table[kk] == I(constants, state).table[kk]
        {
          var src := UseMapsAreFull(maps, kk);
          var src' := UseMapsAreFull(maps', kk);
          DisjointMapsMapKeyToValue(maps, src, kk);
          DisjointMapsMapKeyToValue(maps', src', kk);
          if src == MessageOwner(msg) {
            if src' != HostOwner(id) {
              assert kk in maps'[HostOwner(id)];
              assert false;
            }
            assert maps'[src'][kk] == IMapUnionPreferLeft(maps[src'], maps[src])[kk];
          } else {
            if src != src' {
              assert kk in maps'[src];
              assert false;
            }
          }
        }
      }
    }
  }
}
//#end-elide
