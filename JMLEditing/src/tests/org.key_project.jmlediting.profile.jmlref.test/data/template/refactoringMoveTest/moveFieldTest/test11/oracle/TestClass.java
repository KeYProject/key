package test;

public class TestClass {
    
    /*@
      @ normal_behavior
      @ ensures \result == test.Other.balance;
      @*/
    public int getBalance() {
        return test.Other.balance;
    }
}
