// (former `/*@ code_java_math @*/` and `/*@ spec_bigint_math @*/` class-level pragmas
//  removed: not accepted by JMLtk; the int semantics are set via the .key settings)
class IntSemanticsJava {

    // provable with java integer semantics in code (wraparound of int)
    /*@ normal_behavior
      @  ensures \result == Integer.MIN_VALUE;
      @*/
    int mJava() {
        return Integer.MAX_VALUE + 1;
    }

    // not provable with java integer semantics in code
    /*@ normal_behavior
      @  ensures \result == Integer.MAX_VALUE + 1;
      @*/
    int mJavaWrong() {
        return Integer.MAX_VALUE + 1;
    }
}
