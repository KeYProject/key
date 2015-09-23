package test;

public class TestClass {
    
    public static int balance;

    /*@
      @ normal_behavior
      @ ensures \result == test.TestClass.balance;
      @*/
    public int getBalance() {
        return test.TestClass.balance;
    }
}
