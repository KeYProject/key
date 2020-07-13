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
      @ ensures \result == -4;
      @*/
    public int testBreakLabel() {
        exec { break l2; }
        ccatch (\Return) { return -1; }
        ccatch (\Break) { return -2; }
        ccatch (\Break l1) { return -3; }
        ccatch (\Break l2) { return -4; }
        ccatch (\Continue) { return -5; }
        ccatch (\Continue l1) { return -6; }
        ccatch (\Continue l2) { return -7; }
        ccatch (Throwable t) { return -8; }
          
        return 42;
    }
    
    /*@ public normal_behavior
      @ ensures \result == -7;
      @*/
    public int testContinueLabel() {
        exec { continue l2; }
        ccatch (\Return) { return -1; }
        ccatch (\Break) { return -2; }
        ccatch (\Break l1) { return -3; }
        ccatch (\Break l2) { return -4; }
        ccatch (\Continue) { return -5; }
        ccatch (\Continue l1) { return -6; }
        ccatch (\Continue l2) { return -7; }
        ccatch (Throwable t) { return -8; }
          
        return 42;
    }
    
    /*@ public normal_behavior
      @ ensures \result == -10;
      @*/
    public int testBreakLabelNonmatchingNested() {
        exec {
            l3: {
                exec { break l3; }
                ccatch (\Return) { return -1; }
                ccatch (\Break) { return -2; }
                ccatch (\Break l1) { return -3; }
                ccatch (\Break l2) { return -4; }
                ccatch (\Continue) { return -5; }
                ccatch (\Continue l1) { return -6; }
                ccatch (\Continue l2) { return -7; }
                ccatch (Throwable t) { return -8; }
                return -9;
            }
            return -10;
        } ccatch (\Break l3) { return -11; }
    
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
