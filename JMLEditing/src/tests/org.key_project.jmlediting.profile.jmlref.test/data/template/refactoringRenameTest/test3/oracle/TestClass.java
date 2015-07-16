package test;

public class TestClass {
    private int /*@ spec_public @*/ aNewName;
    
    /*@ normal_behavior
      @ 
      @*/
    public /*@ pure @*/ int getBalance() {
        return this.aNewName;
    }

    /*@ normal_behavior
      @ assignable this.aNewName;
      @*/ 
    public void setBalance(int newBalance) {
        this.aNewName = newBalance;
    }
}
