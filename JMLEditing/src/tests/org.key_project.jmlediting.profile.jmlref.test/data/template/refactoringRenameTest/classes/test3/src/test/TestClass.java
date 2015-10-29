package test;

public class TestClass {
    static int balance;
    
    /*@ normal_behavior
      @ ensures TestClass.balance = newBalance;
      @*/
    void setBalance(int newBalance){
        balance = newBalance;
    }
}