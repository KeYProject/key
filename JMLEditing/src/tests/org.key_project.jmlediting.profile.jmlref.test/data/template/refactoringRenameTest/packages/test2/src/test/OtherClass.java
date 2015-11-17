package test;

public class OtherClass {
    
    /*@ normal_behavior
      @ ensures \result == test.TestClass.balance;
      @ assignable \nothing;
      @*/
    public int getBalance() {
        return test.TestClass.balance;
    }
}