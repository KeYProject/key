package test;

public class TestClass {

    /*@ normal_behavior
      @ ensures \result == test.TestClassOther.getBalance();
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return test.TestClassOther.getBalance();
    }
}
