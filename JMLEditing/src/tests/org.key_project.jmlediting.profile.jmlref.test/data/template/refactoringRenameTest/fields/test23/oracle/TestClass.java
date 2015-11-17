package test;

public class TestClass {
    public int balance;
    
    /*@ normal_behavior
      @ ensures \result == TestClassOther.aNewName;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        return TestClassOther.aNewName;
    }
}
