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


package de.uka.ilkd.key.proof.proofevent;

import de.uka.ilkd.key.logic.PosInOccurrence;


/** Information about a formula that has been removed from a node (the
 * position given is the position of the formula within the new
 * sequent) */
public class NodeChangeRemoveFormula extends NodeChangeARFormula {
    public NodeChangeRemoveFormula ( PosInOccurrence p_pos ) {
	super ( p_pos );
    }

    public String toString () {
	return "Formula removed: " + getPos ();
    }
}
