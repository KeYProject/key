package test;

class TestClass {
    TestClass newName;

    /*@
      @ normal_behavior
      @ ensures this.newName.balance() == newName;
      @*/
    public TestClass balance() {
        return newName;
    }
}