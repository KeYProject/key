package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ ensures \result == newMethdName() + addTo;
      @*/ 
    public int addToBalance(int addTo) {
        return newMethdName() + addTo;
    }
    
    public int newMethdName() {
        return this.balance;
    }
    
    public int getBalance(boolean b) {
        if (b)
            return 5;
        else
            return this.balance;
    }
}