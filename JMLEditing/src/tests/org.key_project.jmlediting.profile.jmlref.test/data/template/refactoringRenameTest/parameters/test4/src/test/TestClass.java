package test;

public class TestClass {
    private int /*@ spec_public @*/ balance;
    private int newBalance;
    

    /*@ normal_behavior
      @ ensures this.newBalance = newBalance;
      @ assignable this.newBalance;
      @*/
    TestClass(int newBalance) {
        this.newBalance = newBalance;
    }
    
    /*@ normal_behavior
      @ ensures this.balance = newBalance;
      @ assignable balance;
      @*/ 
    /**
     * Sets the balance to given newBalance.
     * @param parameter nothing.
     * @param newBalance new balance.
     */
    public void setBalance(boolean parameter, int newBalance) {
        balance = newBalance;
    }
}