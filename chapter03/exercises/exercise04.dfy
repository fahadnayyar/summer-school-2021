// Your goal is to model a lock service that consists of a single server and an
// arbitrary number of clients. The server provides the functionality of an
// exclusive lock. Initially, the server holds the lock. A client can acquire
// the lock (if the lock is currently held by the server) or it can return the
// lock (if it currently holds it). 
//
// Do not model the network. Instead, model the beliefs of the server and each
// of the clients, and allow steps that update a pair of (server, some client)
// simultaneously (skipping the network asynchrony).
//
// Your state machine should reflect the state of the entire distributed system;
// so it’s OK to have a single transition that atomically modifies the state of
// multiple nodes in the system. 

// Here's a helpful boilerplate for the inductive proof structure.

predicate Safety(s:Library) {
  true  // Change me to the important property!
}

predicate Inv(s: Library) {
  Safety(s)
}

lemma SafetyProof()
  ensures forall s :: Init(s) ==> Inv(s)
  ensures forall s, s' :: Inv(s) && Next(s, s') ==> Inv(s')
  ensures forall s :: Inv(s) ==> Safety(s)
{
}
