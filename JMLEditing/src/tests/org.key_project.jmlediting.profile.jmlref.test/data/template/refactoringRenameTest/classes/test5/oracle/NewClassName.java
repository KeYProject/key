package test;

public class NewClassName {
    static int balance;
    
    /*@ normal_behavior
      @ ensures NewClassName.balance = newBalance;
      @*/
    public void setBalance(int newBalance){
        NewClassName.balance = newBalance;
    }
}