/**
 * 
 */
package de.uka.ilkd.key.proof.io.intermediate;

/**
 * TODO.
 * 
 * @author Dominic Scheurer
 */
public class BranchNodeIntermediate extends NodeIntermediate {
    
    private String branchTitle = null;

    public BranchNodeIntermediate(String branchTitle) {
        this.branchTitle = branchTitle;
    }

    public String getBranchTitle() {
        return branchTitle;
    }
    
}