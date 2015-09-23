package thirdPackage;

public class LimitClass {
    public static int overdraftLimit = -100;
    
    /*@ normal_behavior
      @ ensures test.TestClass.balance - amount > overdraftLimit ==> \result == overdraftLimit;
      @ ensures test.TestClass.balance - amount <= overdraftLimit ==> \result == test.TestClass.balance - amount;
      @ assignable test.TestClass.balance;
      @*/
    public static int withdraw(int amount) {
        int newBalance = test.TestClass.balance - amount;
        if (newBalance > overdraftLimit) {
            test.TestClass.balance = overdraftLimit;
            return overdraftLimit;
        }
        else {
            test.TestClass.balance = newBalance;
            return newBalance;
        }
    }
}