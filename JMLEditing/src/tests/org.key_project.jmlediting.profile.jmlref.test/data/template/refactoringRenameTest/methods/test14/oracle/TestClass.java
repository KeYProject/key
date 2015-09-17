package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;

    /*@ normal_behavior
      @ ensures \result == newMethodName() + addTo;
      @*/ 
    public int addToBalance(int addTo) {
        return newMethodName() + addTo;
    }
    
    public int newMethodName() {
        return this.balance;
    }
    
    public TestClass returnMe(boolean b, int amount) {
        return this;
    }
    
    /*@
      @ normal_behavior
      @ ensures \result == returnMe(true, 0).newMethodName();
      @*/
    public int successiveMethodCalls() {
        return returnMe(true, 0).newMethodName();
    }

}