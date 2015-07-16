package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;
    
    /*@ normal_behavior
      @ 
      @*/
    public /*@ pure @*/ int getBalance() {
        return this.balance;
    }

    /*@ normal_behavior
      @ assignable this.balance;
      @*/ 
    public void setBalance(int newBalance) {
        this.balance = newBalance;
    }
}
