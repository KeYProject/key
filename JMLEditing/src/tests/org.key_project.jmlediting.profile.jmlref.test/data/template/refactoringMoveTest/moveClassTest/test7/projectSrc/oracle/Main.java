package mainpack;

public class Main {
    
    /*@ normal_behavior
      @ ensures \result == destPackage.Other.balance;
      @*/
    public static int getBalance() {
        return destPackage.Other.balance;
    }
}