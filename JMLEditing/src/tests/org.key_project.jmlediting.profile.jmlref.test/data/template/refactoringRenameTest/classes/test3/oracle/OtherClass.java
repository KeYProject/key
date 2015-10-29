package test;

public class OtherClass {
    NewClassName testClass = new NewClassName();
    
    /*@
      @ normal_behavior
      @ assignable NewClassName.balance;
      @*/
    void setOtherBalance(int newBalance) {
        testClass.setBalance(newBalance);
    }
}