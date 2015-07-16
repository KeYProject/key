package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;
    
    /*@ normal_behavior
      @ 
      @*/
    public /*@ pure @*/ int getBalance() {
        return balance;
    }

    /*@ normal_behavior
      @ ensures balance = something + \old(balance);
      @ requires balance >= 0;
      @ assignable balance;
      @*/ 
    public void setBalance(int newBalance) {
        balance = newBalance;
    }
}
