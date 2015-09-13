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
    
    public TestClass returnMe(boolean b, int amount) {
        return this;
    }
    
    /*@
      @ normal_behavior
      @ ensures \result == returnMe(true, 0).getBalance();
      @*/
    public int successiveMethodCalls() {
        return returnMe(true, 0).getBalance();
    }

}