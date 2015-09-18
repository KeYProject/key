package test;

public class TestClass {

    public int balance = 5;
    
    //@ invariant balance == 5;
    
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
