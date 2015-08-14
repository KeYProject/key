package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ ensures this.balance = newBalance;
      @ assignable balance;
      @*/ 
    public void setBalance(int newBalance, boolean parameter) {
        balance = newBalance;
    }
}