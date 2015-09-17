package test;

public class NewClassName {
    static int balance;
    
    /*@ normal_behavior
      @ ensures NewClassName.balance = newBalance;
      @ assignable NewClassName.balance;
      @*/
    void setBalance(int newBalance){
        this.balance = newBalance;
    }
}