package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ ensures \result == String.valueOf(newMethodName()) + addTo;
      @*/ 
    public String addToBalance(int addTo) {
        return String.valueOf(newMethodName());
    }
    
    public int newMethodName() {
        return this.balance;
    }
}