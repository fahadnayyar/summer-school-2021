//#title Single-Server Lock Service Model
//#desc A complex state machine
//#desc including a Safety predicate on the state type.

/*
Model a lock service that consists of a single server and an
arbitrary number of clients.

The state of the system includes the server's state (whether the server
knows that some client holds the lock, and if so which one)
and the clients' states (for each client, whether that client knows
it holds the lock).

The system should begin with the server holding the lock.
An acquire step atomically transfers the lock from the server to some client.
(Note that we're not modeling the network yet -- the lock disappears from
the server and appears at a client in a single atomic transition.)
A release step atomically transfers the lock from the client back to the server.

The safety property is that no two clients ever hold the lock
simultaneously.
*/

//#exercisedatatype Constants = Constants(/* You define this ...*/)
//#exercisedatatype Variables = Variables(/* You define this ...*/)
//#start-elide
datatype ServerGrant = Unlocked | Client(id: nat)
datatype ClientRecord = Released | Acquired

datatype Constants = Constants(clientCount: nat)
datatype Variables = Variables(server: ServerGrant, clients: seq<ClientRecord>)
//#end-elide

predicate Init(c:Constants, v:Variables) {
//#exercise  true  // Replace me
//#start-elide
  && v.server.Unlocked?
  && |v.clients| == c.clientCount
  && forall i | 0 <= i < |v.clients| :: v.clients[i].Released?
//#end-elide
}

//#start-elide
predicate Acquire(c:Constants, v:Variables, v':Variables, id:int) {
  && 0 <= id < |v.clients|
  && v.server.Unlocked?
  && v'.server == Client(id)
  && |v'.clients| == |v.clients| == c.clientCount  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |v.clients| ::
      v'.clients[i] == if i == id then Acquired else v.clients[i] )
}

predicate Release(c:Constants, v:Variables, v':Variables, id:int) {
  && 0 <= id < |v.clients|
  && v.clients[id].Acquired?
  && v'.server.Unlocked?
  && |v'.clients| == |v.clients| == c.clientCount  // Don't lose track of any clients.
  && ( forall i | 0 <= i < |v.clients| ::
      v'.clients[i] == if i == id then Released else v.clients[i] )
}

//#end-elide
predicate Next(c:Constants, v:Variables, v':Variables) {
//#exercise  true  // Replace me
//#start-elide
  || ( exists id :: Acquire(c, v, v', id) )
  || ( exists id :: Release(c, v, v', id) )
//#end-elide
}

predicate Safety(c:Constants, v:Variables) {
  // What's a good definition of safety for the lock server? No two clients
  // have the lock simultaneously. Write that here.
//#exercise  false
//#start-elide
  forall i,j ::
    (&& 0 <= i < |v.clients|
    && 0 <= j < |v.clients|
    && v.clients[i].Acquired?
    && v.clients[j].Acquired?) ==> i == j
//#end-elide
}
