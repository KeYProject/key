package test;

public class TestClass {
    static int balance;
    
    /*@ normal_behavior
      @ ensures TestClass.balance = newBalance;
      @ assignable TestClass.balance;
      @*/
    void setBalance(int newBalance){
        this.balance = newBalance;
    }
}