package test;

import java.lang.Integer;

public class TestClass {
    static int balance;
    
    /*@ normal_behavior
      @ ensures \result == Integer.valueOf(balance);
      @*/
    Integer returnString (){
        return Integer.valueOf(balance);
    }
}