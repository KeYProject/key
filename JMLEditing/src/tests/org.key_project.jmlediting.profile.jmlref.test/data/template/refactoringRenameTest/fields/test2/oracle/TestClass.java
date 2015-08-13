package test;

public class TestClass {
    private int /*@ spec_public @*/ tiny;

    /*@ normal_behavior
      @ ensures tiny = something + \old(tiny);
      @ requires tiny >= 0;
      @ assignable tiny;
      @*/ 
    public void setBalance(int newBalance) {
        tiny = newBalance;
    }
}
