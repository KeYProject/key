package test;

public class TestClass {

    /*@ normal_behavior
      @ ensures \result == otherPackage.TestClassOther.newMethodName();
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return otherPackage.TestClassOther.newMethodName();
    }
}
