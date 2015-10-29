package test;

public class TestClass {
    private int /*@ spec_public @*/ aVeryLongNewName;

    /*@ normal_behavior
      @ 
      @ assignable aVeryLongNewName;
      @*/ 
    public void setBalance(int newBalance) {
        aVeryLongNewName = newBalance;
    }
}
