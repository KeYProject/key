package test;

public class OtherClass {
    TestClass testClass = new TestClass();
    
    /*@
      @ normal_behavior
      @ assignable TestClass.balance;
      @*/
    void setOtherBalance(int newBalance) {
        testClass.setBalance(newBalance);
    }
}