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
    
    public TestClass returnMe() {
        return this;
    }
    
    /*@ 
      @ normal_behavior
      @ ensures balance == addToBalance(returnMe().getBalance());
      @*/
    public void doubleBalance() {
        balance = addToBalance(returnMe().getBalance());
    }
}