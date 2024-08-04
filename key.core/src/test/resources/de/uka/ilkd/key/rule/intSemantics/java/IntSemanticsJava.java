/*@ code_java_math @*/        // this is ignored by KeY currently, just for documentation
/*@ spec_bigint_math @*/      // this is the default
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
