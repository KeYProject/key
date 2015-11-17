package test;

public class TestClass {
    public int newName;
    
    /*@ normal_behavior
      @ ensures \result == ((TestClass) get("TestClass")).newName;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        
        return ((TestClass) get("TestClass")).newName;
    }
    
    private Object get(String clazz){
        if (clazz == "TestClass")
            return this;
        else
            return null;
    }
}
