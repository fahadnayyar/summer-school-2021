//#title Two Phase Commit Safety Proof
//#desc Prove that the 2PC distributed system (exercise01) accomplishes the Safety spec (exercise02)

include "model_for_ex03.dfy"

module TwoPCInvariantProof {
  import opened CommitTypes
  import opened Types
  import opened Library
  import opened DistributedSystem
  import opened Obligations

//#start-elide
  predicate VoteMessagesAgreeWithParticipantPreferences(c: Constants, v: Variables)
    requires v.WF(c)
  {
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.VoteMsg?
      && ValidParticipantId(c, msg.sender)
      :: msg.vote == ParticipantConstants(c, msg.sender).preference
    )
  }

  predicate CoordinatorStateSupportedByVote(c: Constants, v: Variables)
    requires v.WF(c)
  {
    (forall idx:HostId |
      && ValidParticipantId(c, idx)
      && CoordinatorVars(c, v).votes[idx].Some?
      :: VoteMsg(idx, CoordinatorVars(c, v).votes[idx].value) in v.network.sentMsgs
    )
  }

//#end-elide
  predicate DecisionMsgsAgreeWithDecision(c: Constants, v: Variables)
    requires v.WF(c)
  {
    (forall msg |
      && msg in v.network.sentMsgs
      && msg.DecisionMsg?
      :: CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v), msg.decision)
    )
  }

  predicate Inv(c: Constants, v: Variables)
  {
    && v.WF(c)
//#start-elide
    && VoteMessagesAgreeWithParticipantPreferences(c, v)
    && CoordinatorStateSupportedByVote(c, v)
//#end-elide
    // We'll give you one invariant to get you started...
    && DecisionMsgsAgreeWithDecision(c, v)
    // ...but you'll need more.
    && Safety(c, v)
  }

  lemma InitImpliesInv(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Inv(c, v)
  {
//#start-elide
    // Nobody has agreed with anything yet, so they agree with both.
    assert AllWithDecisionAgreeWithThisOne(c, v, Commit); // witness.
    assert AllWithDecisionAgreeWithThisOne(c, v, Abort); // witness.
//#end-elide
  }

  lemma InvInductive(c: Constants, v: Variables, v': Variables)
    requires Inv(c, v)
    requires Next(c, v, v')
    ensures Inv(c, v')
  {
//#start-elide
    // The body of this lemma got really big (expanding foralls, case splits,
    // testing asserts) while I was figuring out what invariants were missing
    // ... and fixing a couple of errors in the protocol definition itself.
    // Afterward, nearly all of that text could be deleted.

    var step :| NextStep(c, v, v', step);   // Witness

    // sklomize msg from DecisionMsgsAgreeWithDecision
    forall msg |
      && msg in v'.network.sentMsgs
      && msg.DecisionMsg?
      ensures CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v'), msg.decision)
    {
      var hostid := step.hostid;
      assert Host.Next(c.hosts[hostid], v.hosts[hostid], v'.hosts[hostid], step.msgOps);  // observe trigger
      if msg in v.network.sentMsgs {  // observe trigger
//        assert CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v), msg.decision);
//        assert CoordinatorHost.AllVotesCollected(CoordinatorConstants(c), CoordinatorVars(c,v'));
        // trigger: hey, all the votes are the same!
        // wait why is that true? That's not true when receiving a vote. Hrm.
        assert forall hostIdx:HostId | hostIdx < |CoordinatorVars(c,v).votes| :: CoordinatorVars(c,v').votes[hostIdx] == CoordinatorVars(c,v).votes[hostIdx];
//        assert CoordinatorHost.ObservesResult(CoordinatorConstants(c), CoordinatorVars(c, v'), msg.decision);
//      } else {

      }
    }
//    assert Safety(c, v'); // somehow this trigger is necessary to get the forall above! Bizarre.
//#end-elide
  }

  lemma InvImpliesSafety(c: Constants, v: Variables)
    requires Inv(c, v)
    ensures Safety(c, v)
  { // Trivial, as usual, since safety is a conjunct in Inv.
  }
}
