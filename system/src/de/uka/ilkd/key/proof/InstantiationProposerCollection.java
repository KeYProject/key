// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.TacletApp;


/** 
 * Composite of instantiation proposers.
 */
public class InstantiationProposerCollection implements InstantiationProposer {

    private ImmutableList<InstantiationProposer> proposers 
    		= ImmutableSLList.<InstantiationProposer>nil();

    /**
     * adds an instantiation proposer to the collection
     */
    public void add(InstantiationProposer proposer) {
    	proposers = proposers.append(proposer);
    }
    
    
    public String getProposal(TacletApp app, 
    			      SchemaVariable var, 
			      Services services,
			      Node undoAnchor,
			      ImmutableList<String> previousProposals) {
        for (InstantiationProposer proposer1 : proposers) {
            InstantiationProposer proposer = proposer1;
            String proposal = proposer.getProposal(app,
                    var,
                    services,
                    undoAnchor,
                    previousProposals);
            if (proposal != null) {
                return proposal;
            }
        }
	
	return null;
    }
}
