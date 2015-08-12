package test;

public class TestClass {
    public int newName;
    
    /*@ normal_behavior
      @ ensures get("someClass").newName ==> \result == 0;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        
        if (Integer.toString(newName).equals("5"))
            return 0;
        else
            return 1;
    }
}
