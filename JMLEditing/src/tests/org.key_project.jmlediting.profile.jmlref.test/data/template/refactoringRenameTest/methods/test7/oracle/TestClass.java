package test;

import otherPackage.TestClassOther;

public class TestClass {

    public TestClassOther otherClass = new TestClassOther();

    /*@ normal_behavior
      @ ensures \result == otherClass.newMethodName();
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return otherClass.newMethodName();
    }
}
