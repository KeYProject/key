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
      @ ensures b ==> newMethodName(b) == 5;
      @*/
    public int newMethodName(boolean b) {
        if (b)
            return 5;
        else
            return this.balance;
    }
}