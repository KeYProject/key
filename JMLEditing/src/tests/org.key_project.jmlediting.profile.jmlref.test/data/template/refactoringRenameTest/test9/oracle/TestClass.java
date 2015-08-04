package test;

public class TestClass {
    public int aNewName;
    public TestClassOther otherClass = new TestClassOther();
    
    /*@ normal_behavior
      @ 
      @*/
    public /*@ pure @*/ int getBalance() {
        return aNewName;
    }
    
    /*@ normal_behavior
      @ ensures \result == otherClass.balance;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return otherClass.balance;
    }
}
