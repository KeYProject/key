package test;

class TestClass {
    TestClass newName;

    /*@
      @ normal_behavior
      @ ensures this.newName.newName == newName.newName.balance().newName;
      @*/
    public TestClass balance() {
        return newName;
    }
}