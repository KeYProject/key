package otherPackage;

import test.TestClass;

public class TestClassOther {
    public int balance;
    public TestClass mainClass = new TestClass();

    /*@ normal_behavior
      @ assignable balance;
      @*/ 
    public void setBalance(int newBalance) {
        balance = newBalance;
    }
    
    /*@ normal_behavior
    @ ensures balance == mainClass.balance;
    @ assignable mainClass.balance;
    @*/
    private void accessBalanceFromMainClass(int balance) {
        mainClass.balance = balance;
    }
}
