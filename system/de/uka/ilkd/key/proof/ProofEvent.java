// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;


/** an object indicating that a proof event has happpend */
public class ProofEvent {
    
    private Proof source;


    public ProofEvent(Proof source) {
	this.source=source;
    }
    
    
    /** creates a new proof event the interactive prover where the
     * event initially occured 
     * @param source 
     * @param message a String message
    public ProofEvent(InteractiveProver source, String message) {
	this.source = source;
	this.message = message;
    }
     */


    public Proof getSource() {
	return source;
    }


/*
    public String getMessage() {
	return message;
    }
*/


    /**
     * This information should have its own event, but is currently
     * propagated via this one
     */
    public RuleAppInfo getRuleAppInfo () {
	return ruleAppInfo;
    }

    public ProofEvent(Proof source,
		      RuleAppInfo       rai) {
	this ( source );
	ruleAppInfo = rai;
    }

    private RuleAppInfo ruleAppInfo = null;

}
