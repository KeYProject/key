package otherPackage;

public class ClassWithReferences {
    
    /*@ normal_behavior
      @ ensures \result == test.subpackage.TestClass.balance;
      @*/
    public /*@ pure @*/ int getBalance() {
        return test.subpackage.TestClass.balance;
    }
    
    /*@ normal_behavior
      @ ensures \result == test.subpackage.OtherClass.limit;
      @*/ 
    public /*@ pure @*/ int getLimit() {
        return test.subpackage.OtherClass.limit;
    }
}