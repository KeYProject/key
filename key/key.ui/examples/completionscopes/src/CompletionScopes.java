public class CompletionScopes {
    /*@ public normal_behavior
      @ ensures \result == 0;
      @*/
    public int testCcatchReturnVal() {
        exec { return -1; }
        ccatch (\Return) { return -7; }
        ccatch (\Return int val) { return ++val; }
        ccatch (ArithmeticException t) { return -3; }
        ccatch (Throwable t) { return -4; }
        
        return 42;
    }
    
    /*@ public normal_behavior
      @ ensures \result == -4;
      @*/
    public int testMultCcatchClauses() {
        exec { throw new RuntimeException(); }
        ccatch (ArithmeticException t) { return -3; }
        ccatch (Throwable t) { return -4; }
          
        return 42;
    }
    
    /*@ public normal_behavior
      @ ensures \result == -5;
      @*/
    public int testNestedExec() {
        exec {
            exec { return -1/0; }
            ccatch (\Return) { return -7; }
            ccatch (\Return int val) { return ++val; }
            ccatch (ArithmeticException t) { return -3; }
            ccatch (Throwable t) { return -4; }
        } ccatch (\Return) { return -1; }
        ccatch (ArithmeticException t) { return -5; }
        
        return 42;
    }

}
