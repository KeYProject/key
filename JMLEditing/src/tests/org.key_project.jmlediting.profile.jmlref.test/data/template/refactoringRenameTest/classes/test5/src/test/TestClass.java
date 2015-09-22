package test;

public class TestClass {
    static int balance;
    
    /*@ normal_behavior
      @ ensures TestClass.balance = newBalance;
      @*/
    public void setBalance(int newBalance){
        TestClass.balance = newBalance;
    }
}