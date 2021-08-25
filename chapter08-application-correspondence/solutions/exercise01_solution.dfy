//#title Application Correspondence with Synchronous Sharded KV Store
//#desc How do we prevent a nonsense refinement theorem, for example one that does whatever
//#desc it wants, but abstracts every protocol-level state to the initial spec state, so it
//#desc can refine to a bunch of stutter steps?

include "../../chapter07-async-clients/solutions/exercise01_solution.dfy" //#magicinline

// For reference, go see your or the instructors' solution to chapter06-refine/exercises/exercise01.dfy
module AsyncShardedKVProtocol {
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
