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

package de.uka.ilkd.key.proof.proofevent;

import de.uka.ilkd.key.logic.PosInOccurrence;


/** Information about a formula that has been added or removed from a
 * node */
public abstract class NodeChangeARFormula implements NodeChange {
    
    PosInOccurrence pos;

    public NodeChangeARFormula ( PosInOccurrence p_pos ) {
	pos = p_pos;
    }

    /**
     * @return the position of the formula
     */
    public PosInOccurrence getPos () {
	return pos;
    }

}