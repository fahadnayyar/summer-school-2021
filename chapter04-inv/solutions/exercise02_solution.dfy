//#title Single-Server Lock Service Proof
//#desc A more realistic invariant proof of the previous chapter's lock
//#desc service.

// We provide a correct spec for the lock server here, but leave you
// to define the Safety property to be proven.
// You are welcome to prove correct your own model from chapter03,
// but note that may be too hard or too easy if your spec is broken.

//#inline "../../chapter03-sm/solutions/exercise03_solution.dfy"
//#start-elide
include "../../chapter03-sm/solutions/exercise03_solution.dfy"
//#end-elide

//#start-elide
// Safety doesn't care what server thinks, but to get an *inductive* invariant,
// we need to ensure the server doesn't fall out of sync with the clients'
// beliefs.
predicate ServerAgreesClients(c:Constants, v:Variables) {
  v.server.Unlocked? <==> (forall id | 0 <= id < |v.clients| :: v.clients[id].Released?)
}

//#end-elide
predicate Inv(c:Constants, v:Variables) {
//#exercise  true  // Replace me: probably not strong enough. :v)
//#start-elide
  && Safety(c, v)
  && ServerAgreesClients(c, v)
//#end-elide
}

// Here's your obligation. Probably easiest to break this up into three
// lemmas, each P==>Q becomes requires P ensures Q.
lemma SafetyTheorem(c:Constants, v:Variables, v':Variables)
  ensures Init(c, v) ==> Inv(c, v)
  ensures Inv(c, v) && Next(c, v, v') ==> Inv(c, v')
  ensures Inv(c, v) ==> Safety(c, v)
{
//#start-elide
  if Inv(c, v) && Next(c, v, v') {
    var step :| NextStep(c, v, v', step);        // give a variable name ("step") to what happened in Next
    if step.AcquireStep? {                    // case analysis
//      assert !v'.server.Unlocked?;
      assert !v'.clients[step.id].Released?;  // witness to exist (!forall in ServerAgreesClient)
//      assert Inv(v');
//    } else {
//      assert Inv(v');
    }
  }
//#end-elide
}
