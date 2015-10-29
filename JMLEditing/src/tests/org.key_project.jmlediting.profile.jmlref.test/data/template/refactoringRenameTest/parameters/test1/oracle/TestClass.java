package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ ensures this.balance = aNewName;
      @ assignable balance;
      @*/ 
    public void setBalance(int aNewName) {
        balance = aNewName;
    }
}