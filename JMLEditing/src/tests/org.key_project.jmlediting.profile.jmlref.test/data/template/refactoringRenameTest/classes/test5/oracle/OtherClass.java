package otherPackage;

import test.NewClassName;

public class OtherClass {
    NewClassName testClass = new NewClassName();
    
    /*@ normal_behavior
      @ ensures NewClassName.balance == 0;
      @*/
    void resetBalance() {
        testClass.setBalance(0);
    }
}