package de.uka.ilkd.key.rule;

/**
 * 
 * @author jomi
 *
 *This Exception signals the abort of a rule Application
 *
 */


public class RuleAbortException extends Exception {

    private static final long serialVersionUID = -645034125571021135L;

    public RuleAbortException() {
        super("A rule application has been aborted");
    }
    
    public RuleAbortException(String msg) {
        super(msg);
    }
    
}
