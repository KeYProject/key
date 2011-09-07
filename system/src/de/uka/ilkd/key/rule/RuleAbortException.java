package de.uka.ilkd.key.rule;
import java.lang.*;

/**
 * 
 * @author jomi
 *
 *This Exception signals the abort of a rule Application
 *
 */


public class RuleAbortException extends Exception {

    private static final long serialVersionUID = 1L;
    private String msg;
    
    public RuleAbortException() {
        msg = new String("");
        // TODO Auto-generated constructor stub
    }
    
    public RuleAbortException(String msg) {
        this.msg = msg;
    }
    
    public String getMessage() {
        return msg;
    }
    
}
