package otherPackage;

import thirdPackage.LimitClass;

public class ClassWithReferences {
    
    /*@ normal_behavior
      @ ensures test.TestClass.balance >= LimitClass.overdraftLimit;
      @*/
    public int withdraw(int amount) {
        return LimitClass.withdraw(amount);
    }
}