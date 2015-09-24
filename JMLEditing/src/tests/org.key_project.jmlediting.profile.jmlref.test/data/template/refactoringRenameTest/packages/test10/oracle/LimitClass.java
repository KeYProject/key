package thirdPackage;

public class LimitClass {
    public static int overdraftLimit = -100;
    
    /*@ normal_behavior
      @ ensures newPackageName.TestClass.balance - amount > overdraftLimit ==> \result == overdraftLimit;
      @ ensures newPackageName.TestClass.balance - amount <= overdraftLimit ==> \result == newPackageName.TestClass.balance - amount;
      @ assignable newPackageName.TestClass.balance;
      @*/
    public static int withdraw(int amount) {
        int newBalance = newPackageName.TestClass.balance - amount;
        if (newBalance > overdraftLimit) {
            newPackageName.TestClass.balance = overdraftLimit;
            return overdraftLimit;
        }
        else {
            newPackageName.TestClass.balance = newBalance;
            return newBalance;
        }
    }
}