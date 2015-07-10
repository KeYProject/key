package test;

public class TestClass1 {
    public int /*@ spec_public @*/ balance;
    
    /*@ normal_behavior
      @ pure
      @*/
    public int getBalance() {
        return balance;
    }

    /*@ normal_behavior
      @ 
      @ assignable balance;
      @*/ 
    public void setBalance(int newBalance) {
        balance = newBalance;
    }
}
