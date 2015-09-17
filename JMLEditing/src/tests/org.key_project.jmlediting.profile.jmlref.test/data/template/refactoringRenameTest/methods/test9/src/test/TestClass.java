package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ ensures \result == String.valueOf(getBalance()) + addTo;
      @*/ 
    public String addToBalance(int addTo) {
        return String.valueOf(getBalance());
    }
    
    public int getBalance() {
        return this.balance;
    }
}