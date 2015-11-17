package test;

public class TestClass {
    public int balance;
    
    /*@ normal_behavior
      @ ensures Integer.toString(balance).equals("5") ==> \result == 0;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        
        if (Integer.toString(balance).equals("5"))
            return 0;
        else
            return 1;
    }
    
    /*@ normal_behavior
      @ ensures \result == this.getClass().getDeclaredField("balance").equals(balance);
      @*/
    public boolean doSomething() throws NoSuchFieldException, SecurityException{
        
        return (this.getClass().getDeclaredField("balance").equals(balance));
    }
}
