package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ ensures \result == getBalance() + addTo;
      @*/ 
    public int addToBalance(int addTo) {
        return getBalance() + addTo;
    }
    
    public int getBalance() {
        return this.balance;
    }
    
    /*@ normal_behavior
      @ ensures b ==> getBalance(b) == 5;
      @*/
    public int getBalance(boolean b) {
        if (b)
            return 5;
        else
            return this.balance;
    }
    
    /*@ normal_behavior
      @ ensures amount > 5 ==> getBalance(true);
      @ ensures amount <= 5 ==> getBalance(amount) == balance;
      @*/
    public int getBalance(int amount) {
        if (amount > 5)
            return getBalance(true);
        else
            return balance;
    }
}   