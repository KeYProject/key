package test;

public class TestClass {
    public static int newName;
    
    /*@
      @ normal_behavior
      @ ensures \result == test.TestClass.newName;
      @ assignable \nothing;
      @*/
    public int returnBalance(){
        return test.TestClass.newName;
    }
}