package newPackageName;

public class TestClass {
    public static int balance;
    
    /*@ normal_behavior
      @ ensures \result == newPackageName.TestClass.balance;
      @ assignable \nothing;
      @*/
    public int getBalance() {
        return newPackageName.TestClass.balance;
    }
    
    /*@ normal_behavior
      @ ensures \result == newPackageName.OtherClass.limit;
      @ assignable \nothing;
      @*/
    public int getLimit() {
        return newPackageName.OtherClass.limit;
    }
}