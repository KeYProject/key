package test;

public class TestClass {
    public int balance;
    
    /*@ normal_behavior
      @ ensures get("someClass").balance ==> \result == 0;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        
        if (Integer.toString(balance).equals("5"))
            return 0;
        else
            return 1;
    }
}
