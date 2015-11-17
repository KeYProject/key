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
      @ assignable balance;
      @*/ 
    public void setBalance(int newBalance) {
        balance = newBalance;
    }
    
    /*@ normal_behavior
    @ ensures \result == mainClass.balance;
    @ assignable \nothing;
    @*/
    private int accessBalanceFromMainClass() {
        return mainClass.balance;
    }
}
