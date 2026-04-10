/*@ code_bigint_math @*/      // this is ignored by KeY currently, just for documentation
/*@ spec_bigint_math @*/      // this is the default
class IntSemanticsUncheckedOF {

    // provable with bigint semantics in code and in spec
    /*@ normal_behavior
      @  ensures \result == Integer.MAX_VALUE + 1;
      @*/
    int mBigint() {
        return Integer.MAX_VALUE + 1;
    }

    // not provable with bigint semantics in code and in spec
    /*@ normal_behavior
      @  ensures \result == Integer.MIN_VALUE;
      @*/
    int mBigintWrong() {
        return Integer.MAX_VALUE + 1;
    }
}
