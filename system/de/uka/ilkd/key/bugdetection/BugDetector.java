package de.uka.ilkd.key.bugdetection;

import java.util.Vector;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Node;

public class BugDetector {
    
    MsgMgt msgMgt;
    Services services;
    /**If true then an interactive side proof will be created when running {@code FalsifiabilityPreservation.check()}. 
     * If false then a side-proof will be automatically run in the background when running {@code FalsifiabilityPreservation.check()}.*/
    boolean fpCheckInteractive=true;

    public BugDetector(Services services){
	this.services = services;
    }
    public void run(Node n){
	msgMgt = new MsgMgt();
	FalsifiabilityPreservation fp = new FalsifiabilityPreservation(this,n);
	fp.collectFPConditions();
    }
    
    
    /** Message managment. Collects Messages, Warnings, and Errors */
    public static class MsgMgt {
	private Vector<String> warnings = new Vector<String>();

	/**@param severity  0=comment, 1=minor, ..., 3=probably a bug	 */
	public void warning(String s, int severity) {
	    warnings.add(s);
	}
    }


    public static class UnhandledCase extends RuntimeException{
        public UnhandledCase(String s){
            super("UnhandledCase: "+s);
        }
    }
    
    public static class UnknownCalculus extends RuntimeException{
	public UnknownCalculus(String s, Term t){
	    super("Unexpected structure of calculus rule or formula. "+
		    (s!=null?s:"")+(t!=null?" Problematic Term is:"+t.toString():""));
	}
    }
}
