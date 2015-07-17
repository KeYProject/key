package test;

public class TestClassOther {
    public int balance;
    public TestClass mainClass = new TestClass();
    
    /*@ normal_behavior
      @ 
      @*/
    public /*@ pure @*/ int getBalance() {
        return balance;
    }
    
    /*@ normal_behavior
    @ ensures \result == mainClass.balance;
    @ assignable \nothing;
    @*/
    private int accessBalanceFromMainClass() {
        return mainClass.getBalance();
    }
}
