package test;

public class TestClass {
    
    //@ invariant TestClass.balance > 0;
    public static int balance;

    /*@
      @ normal_behavior
      @ ensures \result == test.TestClass.balance;
      @*/
    public int getBalance() {
        return test.TestClass.balance;
    }
}
