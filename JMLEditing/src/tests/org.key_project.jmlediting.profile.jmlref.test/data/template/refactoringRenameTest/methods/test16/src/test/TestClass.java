package test;

public class TestClass {

    /*@ normal_behavior
      @ ensures \result == otherPackage.TestClassOther.getBalance();
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return otherPackage.TestClassOther.getBalance();
    }
}
