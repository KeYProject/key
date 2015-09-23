package test;

import java.lang.String;

public class TestClass {
    static int balance;
    
    /*@ normal_behavior
      @ ensures \result == String.valueOf(balance);
      @*/
    String returnString (){
        return String.valueOf(balance);
    }
}