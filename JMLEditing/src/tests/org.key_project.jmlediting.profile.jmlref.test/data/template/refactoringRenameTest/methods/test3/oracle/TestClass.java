package test;

public class TestClass {
    private int /*@ spec_public @*/ aNewName;

    /*@ normal_behavior
      @ assignable this.aNewName;
      @*/ 
    public void setBalance(int balance) {
        this.aNewName = balance;
    }
}
