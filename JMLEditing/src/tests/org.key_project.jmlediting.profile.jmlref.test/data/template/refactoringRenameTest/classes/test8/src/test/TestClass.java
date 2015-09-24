package test;

public class TestClass {
    
    /*@
      @ normal_behavior
      @ ensures \result == (TestClass) someClass;
      @*/
    TestClass castToTestClass(Object someClass) {
        if (someClass instanceof TestClass){
            return (TestClass) someClass;
        }
        else {
            return null;
        }
    }
}