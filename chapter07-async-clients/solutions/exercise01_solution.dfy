//#title KV Spec with Asynchronous Client Interface
//#desc Modify the KV spec to encode asynchronous client requests.

// Note that we're unconcerned with the protocol at the moment;
// the goal here is only to modify the spec to capture linearizability,
// a property that arises because client requests take time to process.

//#start-elide TODO(manos) need to exercisify this experiment
include "../../library/Library.dfy"

// See chapter06-refine/exercises/exercise01 for documentation on this module.
// Here I give concrete types because I want to play around with an instance
// of this module.
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
}

// This module defines a Map state machine that serves as the system specification.
// In separate steps it should collect input requests from the client, service
// them atomically, then deliver output replies. Requests that are outstanding
// simultaneously can be serviced in any order (since the spec can
// nondeterministically select the order to service them); requests that don't
// overlap must affect each other in temporal order (linearizability).

module MapSpec {
  import opened Types

// TODO(jonh)add nonce
  datatype Input =
    | InsertRequest(key:Key, value:Value)
    | QueryRequest(key:Key)

  datatype Output =
    | InsertReply(request: Input)
    | QueryReply(request: Input, output: Value)

  datatype Variables = Variables(mapp:map<Key, Value>,
    requests:multiset<Input>, replies:multiset<Output>)
    //TODO(jonh) go to set; prevent duplicate insertion

  predicate Init(v: Variables)
  {
    && v.mapp == InitialMap()
    && v.requests == multiset{}
    && v.replies == multiset{}
  }

  predicate AcceptRequest(v:Variables, v':Variables, request: Input)
  {
    && v' == v.(requests := v.requests + multiset{request})
  }

  predicate DeliverReply(v:Variables, v':Variables, reply: Output)
  {
    && reply in v.replies
    && v' == v.(replies := v.replies - multiset{reply})
  }

  predicate InsertOp(v:Variables, v':Variables, request: Input)
  {
    // A well-formed condition: we're not even gonna talk about keys other than AllKeys().
    && request.key in AllKeys()
    // Don't do a request that a client hasn't asked for.
    && request in v.requests
    && request.InsertRequest?
    && v' == v.(
      // Replace key with value. v.mapp domain remains AllKeys().
      mapp := v.mapp[request.key := request.value],
      // Remove request from those awaiting service
      requests := v.requests - multiset{request},
      // Add reply marking Insert complete so client can learn about it
      replies := v.replies + multiset{InsertReply(request)})
  }

  predicate QueryOp(v:Variables, v':Variables, request: Input, output: Value)
  {
    && request.key in AllKeys()
    && request.key in v.mapp
    // Don't do a request that a client hasn't asked for.
    && request in v.requests
    && request.QueryRequest?
    && output == v.mapp[request.key]
    && v' == v.(
      // (No change to mapp state)
      // Remove request from those awaiting service
      requests := v.requests - multiset{request},
      // Add reply marking Insert complete so client can learn about it
      replies := v.replies + multiset{QueryReply(request, output)})
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

  // We'll realize behaviors explicitly (as a sequence of states) so we can goof around
  // with proofs about what this spec might say.
  predicate ValidBehavior(execution:seq<Variables>, steps:seq<Step>)
  {
    && |execution| == |steps| + 1
    && Init(execution[0])
    && (forall i | 0<=i<|steps| :: NextStep(execution[i], execution[i+1], steps[i]))
  }

  // Some point tests to confirm that the protocol allows various desired behavior.
  lemma PseudoLiveness()
  {
    // Here's a run that orders a simultaneously-outstanding set of inserts one way.
    var req3 := InsertRequest("cat", 3);
    var req4 := InsertRequest("cat", 4);
    var executionA := [
      Variables(InitialMap(), multiset{}, multiset{}),
      Variables(InitialMap(), multiset{req4}, multiset{}),
      Variables(InitialMap(), multiset{req3, req4}, multiset{}),
      Variables(InitialMap()["cat" := 4], multiset{req3}, multiset{InsertReply(req4)}),
      Variables(InitialMap()["cat" := 3], multiset{}, multiset{InsertReply(req4), InsertReply(req3)}),
      Variables(InitialMap()["cat" := 3], multiset{}, multiset{InsertReply(req3)}),
      Variables(InitialMap()["cat" := 3], multiset{}, multiset{})
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
      Variables(InitialMap(), multiset{}, multiset{}),
      Variables(InitialMap(), multiset{req4}, multiset{}),
      Variables(InitialMap(), multiset{req3, req4}, multiset{}),
      Variables(InitialMap()["cat" := 3], multiset{req4}, multiset{InsertReply(req3)}),
      Variables(InitialMap()["cat" := 4], multiset{}, multiset{InsertReply(req4), InsertReply(req3)}),
      Variables(InitialMap()["cat" := 4], multiset{}, multiset{InsertReply(req3)}),
      Variables(InitialMap()["cat" := 4], multiset{}, multiset{})
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
      Variables(InitialMap(), multiset{}, multiset{}),
      Variables(InitialMap(), multiset{req3}, multiset{}),
      Variables(InitialMap()["cat" := 3], multiset{}, multiset{InsertReply(req3)}),
      Variables(InitialMap()["cat" := 3], multiset{}, multiset{}),
      Variables(InitialMap()["cat" := 3], multiset{req4}, multiset{}),
      Variables(InitialMap()["cat" := 4], multiset{}, multiset{InsertReply(req4)}),
      Variables(InitialMap()["cat" := 4], multiset{}, multiset{})
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
//#end-elide TODO(manos) need to exercisify this experiment
