//#title Property Lemmas for Atomic Commit
//#desc The state machine model captures AC2 nicely,
//#desc but let's make it very clear that the model also obeys
//#desc AC1, AC3 and AC4.

/*
 * To increase our confidence that our state machine spec from
 * exercise02 accurately defines our goal,
 * we can state and prove some properties about it.
 *
 * AC1: All processes that reach a decision reach the same one.
 * AC3: The Commit decision can only be reached if all processes prefer Yes.
 * AC4: If all processes prefer Yes, then the decision must be Commit.
 *
 * We'll not bother with AC2 because it can't be stated as a safety
 * property, however it should be abundantly clear from the Next
 * action of the state machine model.
 * AC2: (stability) A process cannot reverse its decision after it has reached one.
 *
 * We'll not bother with AC5 because it's a liveness property, which
 * is outside the scope of this course.
 * AC5: (liveness) All processes eventually decide.
 *
 * If you wrote a broken spec, it will be difficult to prove these properties
 * on it.
 */

include "exercise02_solution.dfy" //#magicinclude

// We don't state AC2 because it's a history property, not stateable as a
// single-state safety property. But it should be clearly evident from the
// state machine structure.
// We don't state AC5 because it's a liveness property, which is out of scope
// for this course.
module AtomicCommitProperties {
  import opened CommitTypes
  import opened AtomicCommit

  // Defining this predicate makes the definitions of the AC properties
  // much easier to read (and in fact easier for Dafny to automate).
  predicate AllWithDecisionAgreeWithThisOne(c: Constants, v: Variables, decision: Decision)
    requires c.WF()
    requires v.WF(c)
  {
//#exercise    false // Replace me
//#start-elide
    && (v.coordinatorDecision.Some? ==> v.coordinatorDecision.value == decision)
    && (forall idx:ParticipantId
      | c.ValidParticipant(idx) && v.participantDecisions[idx].Some?
      :: v.participantDecisions[idx].value == decision)
//#end-elide
  }

  predicate SafetyAC1(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
//#exercise    false // Replace me
//#start-elide
    // All hosts that reach a decision reach the same one
    || AllWithDecisionAgreeWithThisOne(c, v, Commit)
    || AllWithDecisionAgreeWithThisOne(c, v, Abort)
//#end-elide
  }

  // AC2 can't be stated about a single state; the "code reviewer"
  // should be able to confirm it by reading the state machine spec
  // from exercise02.

  predicate SafetyAC3(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
//#exercise    false // Replace me
//#start-elide
    && (exists idx:ParticipantId
      :: c.ValidParticipant(idx) && c.preferences[idx].No?)
      ==> AllWithDecisionAgreeWithThisOne(c, v, Abort)
//#end-elide
  }

  predicate SafetyAC4(c: Constants, v: Variables)
    requires c.WF()
    requires v.WF(c)
  {
//#exercise    false // Replace me
//#start-elide
    && (forall idx:ParticipantId
        | c.ValidParticipant(idx) :: c.preferences[idx].Yes?)
      ==> AllWithDecisionAgreeWithThisOne(c, v, Commit)
//#end-elide
  }

  // AC5 is a liveness proprety, we're definitely going to ignore it.

  //#instructor Player 1
  predicate Safety(c: Constants, v: Variables)
  {
    && c.WF()
    && v.WF(c)
    && SafetyAC1(c, v)
    && SafetyAC3(c, v)
    && SafetyAC4(c, v)
  }

  lemma SafetyInit(c: Constants, v: Variables)
    requires Init(c, v)
    ensures Safety(c, v)
  {
  }

  lemma SafetyNext(c: Constants, v: Variables, v': Variables)
    requires Safety(c, v)
    requires Next(c, v, v')
    ensures Safety(c, v')
  {
  }
}
