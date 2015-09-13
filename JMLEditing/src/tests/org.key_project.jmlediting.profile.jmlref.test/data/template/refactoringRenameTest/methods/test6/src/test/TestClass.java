package test;

public class TestClass {

    public TestClassOther otherClass = new TestClassOther();

    /*@ normal_behavior
      @ ensures \result == getBalance();
      @ assignable \nothing;
      @*/
    public int accessOwnBalance() {
        return getBalance();
    }
    
    public int getBalance() {
        return balance;
    }
}
