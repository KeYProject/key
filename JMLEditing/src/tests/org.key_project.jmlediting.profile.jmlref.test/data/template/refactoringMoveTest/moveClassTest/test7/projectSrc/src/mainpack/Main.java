package mainpack;

public class Main {
    
    /*@ normal_behavior
      @ ensures \result == mainpack.Other.balance;
      @*/
    public static int getBalance() {
        return mainpack.Other.balance;
    }
}