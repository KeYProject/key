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

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.TacletApp;


/** 
 * Provides proposals for schema variable instantiations.
 */
public interface InstantiationProposer {

    /**
     * Returns an instantiation proposal for the schema variable var.
     * @param app the taclet app
     * @param var the schema variable to be instantiated
     * @param services pointer to services object
     * @param undoAnchor node to be used as undo anchor
     * @param previousProposals a list of other proposals which should be taken
     *                          into account (e.g. for name uniqueness), or null
     */
    public String getProposal(TacletApp app, 
    			      SchemaVariable var, 
			      Services services,
			      Node undoAnchor,
			      ImmutableList<String> previousProposals);
}