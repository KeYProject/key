package test;

public class TestClass {
    private int /*@ spec_public @*/ aNewName;
    private int someOtherField;

    /*@ normal_behavior
      @ ensures aNewName = newBalance;
      @ requires aNewName >= 0;
      @ assignable someOtherField, aNewName;
      @*/ 
    public void setBalance(int newBalance) {
        someOtherField = 0;
        aNewName = newBalance;
    }
}
