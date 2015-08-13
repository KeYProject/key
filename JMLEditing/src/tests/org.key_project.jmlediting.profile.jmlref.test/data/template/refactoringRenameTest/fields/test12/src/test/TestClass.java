package test;

class TestClass {
    TestClass balance;

    /*@
      @ normal_behavior
      @ ensures this.balance.balance() == balance;
      @*/
    public TestClass balance() {
        return balance;
    }
}