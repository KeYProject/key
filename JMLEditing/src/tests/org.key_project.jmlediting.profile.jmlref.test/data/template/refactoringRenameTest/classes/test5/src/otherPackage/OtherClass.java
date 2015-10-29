package otherPackage;

import test.TestClass;

public class OtherClass {
    TestClass testClass = new TestClass();
    
    /*@ normal_behavior
      @ ensures TestClass.balance == 0;
      @*/
    void resetBalance() {
        testClass.setBalance(0);
    }
}