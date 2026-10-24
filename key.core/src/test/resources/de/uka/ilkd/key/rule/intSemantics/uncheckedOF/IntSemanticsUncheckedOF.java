// (former `/*@ code_bigint_math @*/` and `/*@ spec_bigint_math @*/` class-level pragmas
//  removed: not accepted by JMLtk; the int semantics are set via the .key settings)
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
