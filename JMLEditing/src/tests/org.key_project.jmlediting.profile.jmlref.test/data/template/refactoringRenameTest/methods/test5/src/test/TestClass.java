package test;

public class TestClass {

    public TestClassOther otherClass = new TestClassOther();

    /*@ normal_behavior
      @ ensures \result == otherClass.getBalance();
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return otherClass.getBalance();
    }
}
