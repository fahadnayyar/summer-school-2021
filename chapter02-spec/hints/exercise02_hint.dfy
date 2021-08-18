// Here's the body of test_prime. It's correct (you're welcome),
// but the proof won't go through yet.
method test_prime(candidate:nat) returns (result:bool)
    ensures result == IsPrime(candidate)
{
  // Three of these lines are the while version of for(f=0; f<candidate; f++){}.
  var factor := 2;
  while (factor < candidate)
  {
    // If this factor divides candidate, we've found a counterexample;
    // candidate isn't prime.
    if candidate % factor == 0 {
      return false;
    }
    factor := factor + 1;
  }
  // We tested every possible factor, and none divided candidate. candidate is prime.
  return true;
}
