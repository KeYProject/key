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
    
    public TestClass returnMe() {
        return this;
    }
    
    /*@
      @ normal_behavior
      @ ensures \result == (returnMe()).newMethodName();
      @*/
    public int successiveMethodCalls() {
        return (returnMe()).newMethodName();
    }

}