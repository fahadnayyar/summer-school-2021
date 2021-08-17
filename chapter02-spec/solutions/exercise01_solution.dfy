//#title IsPrime I
//#desc Basic specification.
// Implement a predicate that tells whether a natural number is prime.

//#start-elide
predicate divides(factor:nat, candidate:nat)
  requires 1<=factor
{
  candidate % factor == 0
}

//#end-elide
predicate IsPrime(candidate:nat)
{
//#exercise  && false // Replace me
//#start-elide
  && 1 < candidate
  && forall factor :: 1 < factor < candidate ==> !divides(factor, candidate)
//#end-elide
}

method Main()
{
  assert !IsPrime(0);
  assert !IsPrime(1);
  assert IsPrime(2);
  assert IsPrime(3);
//#start-elide
  assert divides(2, 6);
//#end-elide
  assert !IsPrime(6);
  assert IsPrime(7);
//#start-elide
  assert divides(3, 9);
//#end-elide
  assert !IsPrime(9);
}
