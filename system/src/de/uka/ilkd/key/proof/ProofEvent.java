// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.proof.proofevent.RuleAppInfo;


/** an object indicating that a proof event has happpend */
public class ProofEvent {
    
    private Proof source;


    /** creates a new proof event the interactive prover where the
     * event initially occured 
     * @param source 
     */
    public ProofEvent(Proof source) {
	this.source=source;
    }
    
    
    public Proof getSource() {
	return source;
    }

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