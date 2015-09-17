package otherPackage;

public class TestClassOther {
    public static int balance;
    
    /*@ normal_behavior
      @ ensures \result == balance;
      @*/
    public static /*@ pure @*/ int getBalance() {
        return balance;
    }

    /*@ normal_behavior
      @ assignable balance;
      @*/ 
    public void setBalance(int newBalance) {
        balance = newBalance;
    }
}
