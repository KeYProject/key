package otherPackage;

public class ClassWithReferences {
    
    /*@ normal_behavior
      @ ensures \result == newPackageName.TestClass.balance;
      @*/
    public /*@ pure @*/ int getBalance() {
        return newPackageName.TestClass.balance;
    }
    
    /*@ normal_behavior
      @ ensures \result == newPackageName.OtherClass.limit;
      @*/ 
    public /*@ pure @*/ int getLimit() {
        return newPackageName.OtherClass.limit;
    }
}