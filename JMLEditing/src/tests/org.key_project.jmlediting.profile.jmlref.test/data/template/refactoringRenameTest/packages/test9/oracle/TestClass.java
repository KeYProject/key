package test;

public class TestClass {
    public static int emptyPackage;
    
    /*@ normal_behavior
      @ ensures \result == test.TestClass.emptyPackage;
      @ assignable \nothing;
      @*/
    public int getBalance() {
        return test.TestClass.emptyPackage;
    }
}