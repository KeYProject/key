package test;

import otherPackage.TestClassOther;

public class TestClass {
    public int balance;
    public TestClassOther otherClass = new TestClassOther();
    
    /*@ normal_behavior
      @ 
      @*/
    public /*@ pure @*/ int getBalance() {
        return balance;
    }

    /*@ normal_behavior
      @ assignable balance;
      @*/ 
    public void setBalance(int newBalance) {
        balance = newBalance;
    }
    
    /*@ normal_behavior
      @ ensures \result == otherClass.balance;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return otherClass.balance;
    }
}
