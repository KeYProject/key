package test;

public class NewClassName {
    static int balance;
    
    /*@ normal_behavior
      @ ensures NewClassName.balance = newBalance;
      @*/
    void setBalance(int newBalance){
        balance = newBalance;
    }
    
    /*@ normal_behavior
      @ ensures \result == NewClassName.balance;
      @ assignable \nothing;
      @*/
    static int getBalance() {
        return NewClassName.balance;
    }
}