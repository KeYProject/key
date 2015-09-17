package newPackageName;

public class OtherClass {
    
    /*@ normal_behavior
      @ ensures \result == newPackageName.TestClass.balance;
      @ assignable \nothing;
      @*/
    public int getBalance() {
        return newPackageName.TestClass.balance;
    }
}