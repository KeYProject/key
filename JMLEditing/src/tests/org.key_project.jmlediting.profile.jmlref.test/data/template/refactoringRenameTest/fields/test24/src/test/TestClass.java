package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;
    private int someOtherField;

    /*@ normal_behavior
      @ ensures balance = newBalance;
      @ requires balance >= 0;
      @ assignable someOtherField, balance;
      @*/ 
    public void setBalance(int newBalance) {
        someOtherField = 0;
        balance = newBalance;
    }
}
