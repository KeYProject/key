package test;

public class NewClassName {
    public static int balance;
    
    /*@
      @ normal_behavior
      @ ensures \result == test.NewClassName.balance;
      @ assignable \nothing;
      @*/
    public int returnBalance(){
        return test.NewClassName.balance;
    }
}