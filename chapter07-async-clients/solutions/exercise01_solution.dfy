//#title KV Spec with Asynchronous Client Interface
//#desc Modify the KV spec to encode asynchronous client requests.

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
//#exercise    // TODO Add stuff here
//#start-elide
    && v.requests == {}
    && v.replies == {}
//#end-elide
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

  predicate InsertOp(v:Variables, v':Variables, request: Input)
  {
//#exercise    false // TODO Replace me. Reference chapter06/exercises/exercise01.dfy InsertOp.
//#start-elide
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
//#end-elide
  }

  predicate QueryOp(v:Variables, v':Variables, request: Input, output: Value)
  {
//#exercise    false // TODO Replace me. Reference chapter06/exercises/exercise01.dfy QueryOp.
//#start-elide
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
//#end-elide
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
