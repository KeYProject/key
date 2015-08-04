package test;

class TestClass {
    TestClass test;

    /*@
      @ normal_behavior
      @ ensures this.test.test == test.test.test().test;
      @*/
    public TestClass test() {
        return test;
    }
}