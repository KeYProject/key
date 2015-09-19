package test;

public class TestClass {
    public int balance;
    
    /*@ normal_behavior
      @ ensures \result == ((TestClass) get("TestClass")).balance;
      @ assignable \nothing;
      @*/
    public int accessBalanceFromOtherClass() {
        
        return ((TestClass) get("TestClass")).balance;
    }
    
    private Object get(String clazz){
        if (clazz == "TestClass")
            return this;
        else
            return null;
    }
}
