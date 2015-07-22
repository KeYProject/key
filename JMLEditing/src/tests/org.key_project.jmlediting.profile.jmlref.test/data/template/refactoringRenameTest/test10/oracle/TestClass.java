package test;

class TestClass {
    TestClass newName;

    /*@
      @ normal_behavior
      @ ensures this.newName.newName == newName.newName.test().newName;
      @*/
    public TestClass test() {
        return newName;
    }
}