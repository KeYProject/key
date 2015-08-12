package test;

public class TestClass {
    public int aNewName;
    public TestClassOther otherClass = new TestClassOther();
    
    /*@ normal_behavior
      @ ensures Integer.toString(aNewName).equals("5") ==> \result == 0;
      @ ensures !Integer.toString(aNewName).equals("5") ==> \result == otherClass.balance;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        
        if (Integer.toString(aNewName).equals("5"))
            return 0;
        else
            return otherClass.balance;
    }
}
