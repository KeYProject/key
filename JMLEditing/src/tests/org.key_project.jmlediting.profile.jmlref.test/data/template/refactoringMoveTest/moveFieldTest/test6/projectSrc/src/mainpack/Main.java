package mainpack;

public class Main {
    
    /*@ normal_behavior
      @ ensures \result == Other.balance;
      @*/
    public static int getBalance() {
        return Other.balance;
    }
}