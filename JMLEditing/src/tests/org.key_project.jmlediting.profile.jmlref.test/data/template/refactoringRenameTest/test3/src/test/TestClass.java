package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ assignable this.balance;
      @*/ 
    public void setBalance(int balance) {
        this.balance = balance;
    }
}
