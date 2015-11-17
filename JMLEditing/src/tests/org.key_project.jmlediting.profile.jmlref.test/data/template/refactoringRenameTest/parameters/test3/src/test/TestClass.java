package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ ensures this.balance = newBalance;
      @ assignable balance;
      @*/ 
    public void setBalance(boolean parameter, int newBalance) {
        balance = newBalance;
    }
}