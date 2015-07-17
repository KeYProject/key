package test;

public class TestClass {
    public int balance;
    public TestClassOther otherClass = new TestClassOther();
    
    /*@ normal_behavior
      @ ensures \result == otherClass.balance;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return otherClass.balance;
    }
}
