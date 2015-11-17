package test;

public class TestClass {

    /*@ normal_behavior
      @ ensures \result == test.TestClassOther.newMethodName();
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return test.TestClassOther.newMethodName();
    }
}
