package otherPackage;

public class ClassWithReferences {
    
    /*@ normal_behavior
      @ ensures \result == test.TestClass.balance;
      @*/
    public /*@ pure @*/ int getBalance() {
        return test.TestClass.balance;
    }
    
    /*@ normal_behavior
      @ ensures \result == test.newPackageName.OtherClass.limit;
      @*/ 
    public /*@ pure @*/ int getLimit() {
        return test.newPackageName.OtherClass.limit;
    }
}