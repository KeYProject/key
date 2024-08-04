/*@ code_safe_math @*/        // this is ignored by KeY currently, just for documentation
/*@ spec_bigint_math @*/      // this is the default
class IntSemanticsCheckedOF {

    // provable with overflow check taclet option, since no overflow can occur with this precondition
    /*@ normal_behavior
      @  requires Integer.MIN_VALUE <= a + b <= Integer.MAX_VALUE;
      @  ensures \result == a + b;
      @*/
    int mOFCheck(int a, int b) {
        return a + b;
    }

    // not provable with overflow check taclet option (separate branch for overflow check stays open)
    /*@ normal_behavior
      @  ensures \result == a + b;
      @*/
    int mOFCheckWrong(int a, int b) {
        return a + b;
    }
}
