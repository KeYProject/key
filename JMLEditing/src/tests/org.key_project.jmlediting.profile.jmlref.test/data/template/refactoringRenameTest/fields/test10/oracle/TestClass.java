package test;

public class TestClass {
    //@ invariant aNewName == 5;
    public int aNewName = 5;
    
    /*@ normal_behavior
      @ assignable aNewName;
      @*/ 
    public void setBalance(int newBalance) {
        if (newBalance == 5)
            aNewName = newBalance;
        else
            aNewName = 5;
    }
}
