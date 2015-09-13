package test;

public class TestClass {
    private String /*@ spec_public @*/ balance = "0";

    /*@ normal_behavior
      @ ensures returnMe().newMethodName().equals("500") ==> true;
      @*/ 
    public Boolean addToBalance(int addTo) {
        return returnMe().newMethodName().equals("500");
    }
    
    public String newMethodName() {
        return this.balance;
    }
    
    public TestClass returnMe() {
        return this;
    }
}