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
    
    public int getBalance(boolean b) {
        if (b)
            return 5;
        else
            return this.balance;
    }
}