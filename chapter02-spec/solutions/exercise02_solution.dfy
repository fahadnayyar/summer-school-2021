//#title IsPrime II
//#desc Working with an implementation proof

// Here's a correct definition of IsPrime.
// Take another little detour to implementation-land by writing a method
// `test_prime` that implements IsPrime with an imperative while() loop.

predicate divides(factor:nat, candidate:nat)
  requires 1<=factor
{
  candidate % factor == 0
}

predicate IsPrime(candidate:nat)
{
  && 1<candidate
  && ( forall factor :: 1 < factor < candidate ==> !divides(factor, candidate) )
}

// Convincing the proof to go through requires adding
// a loop invariant and a triggering assert.
method test_prime(candidate:nat) returns (result:bool)
  requires 1<candidate
  ensures result == IsPrime(candidate)
{
//#exercise  // Fill in the body.
//#start-elide
  var factor := 2;
  while (factor < candidate)
    // This loop invariant completes an inductive proof of the
    // body of IsPrime. Go look at the IsPrime definition and
    // see how this forall relates to it.
    // Note that when factor == candidate, this is IsPrime.
    // Also note that, when the while loop exists, candidate<=factor.
    invariant forall smallerfactor :: 1 < smallerfactor < factor ==> !divides(smallerfactor, candidate)
  {
    if candidate % factor == 0 {
      // This assert is needed to witness that !IsPrime.
      // !IsPrime is !forall !divides, which rewrites to exists divides.
      // Dafny rarely triggers its way to a guess for an exists (apparently
      // it's tough for Z3), but mention a witness and Z3's happy.
      assert divides(factor, candidate);
      return false;
    }
    factor := factor + 1;
  }
  return true;
//#end-elide
}

method Main()
{
  var isprime3 := test_prime(3);
  assert isprime3;
  var isprime4 := test_prime(4);
  assert divides(2, 4);
  assert !isprime4;
  var isprime5 := test_prime(5);
  assert isprime5;
}
