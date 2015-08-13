package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ ensures this.balance = aNewName;
      @ assignable balance;
      @*/ 
    public void setBalance(boolean parameter, int aNewName) {
        balance = aNewName;
    }
}