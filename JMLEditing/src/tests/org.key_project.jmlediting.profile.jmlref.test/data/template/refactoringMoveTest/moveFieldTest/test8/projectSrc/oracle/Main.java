package mainpack;

import destPackage.Dest;

public class Main {
    
    /*@ normal_behavior
      @ ensures \result == Dest.balance;
      @*/
    public static int getBalance() {
        return Dest.balance;
    }
}