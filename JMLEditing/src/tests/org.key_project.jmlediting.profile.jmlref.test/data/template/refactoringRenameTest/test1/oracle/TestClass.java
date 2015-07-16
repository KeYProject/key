package test;

public class TestClass {
    private int /*@ spec_public @*/ aVeryLongNewName;
    
    /*@ normal_behavior
      @ pure
      @*/
    public int getBalance() {
        return aVeryLongNewName;
    }

    /*@ normal_behavior
      @ 
      @ assignable aVeryLongNewName;
      @*/ 
    public void setBalance(int newBalance) {
        aVeryLongNewName = newBalance;
    }
}
