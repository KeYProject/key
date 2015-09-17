package test;

public class NewClassName {
    static int balance;
    
    /*@ normal_behavior
      @ ensures NewClassName.balance = newBalance;
      @*/
    void setBalance(int newBalance){
        balance = newBalance;
    }
}