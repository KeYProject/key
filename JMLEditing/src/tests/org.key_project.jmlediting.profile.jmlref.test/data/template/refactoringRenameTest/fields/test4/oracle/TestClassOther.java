package test;

public class TestClassOther {
    public int balance;
    
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
}
