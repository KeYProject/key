package test;

public class TestClass {
    //@ invariant balance == 5;
    public int balance = 5;
    
    /*@ normal_behavior
      @ assignable balance;
      @*/ 
    public void setBalance(int newBalance) {
        if (newBalance == 5)
            balance = newBalance;
        else
            balance = 5;
    }
}
