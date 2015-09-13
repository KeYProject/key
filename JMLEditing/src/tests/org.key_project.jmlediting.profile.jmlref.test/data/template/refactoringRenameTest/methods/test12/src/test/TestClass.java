package test;

public class TestClass {
    private String /*@ spec_public @*/ balance = "0";

    /*@ normal_behavior
      @ ensures returnMe().getBalance().equals("500") ==> true;
      @*/ 
    public Boolean addToBalance(int addTo) {
        return returnMe().getBalance().equals("500");
    }
    
    public String getBalance() {
        return this.balance;
    }
    
    public TestClass returnMe() {
        return this;
    }
}