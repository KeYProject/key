// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.logic;

/**
 * This class is used to hold information about modified formulas.
 * @see SequentChangeInfo
 */
public class FormulaChangeInfo {
    /** position within the original formula */
    private final PosInOccurrence    positionOfModification;
    /** modified formula */
    private final ConstrainedFormula newFormula;

    public FormulaChangeInfo(PosInOccurrence positionOfModification,
			     ConstrainedFormula newFormula) {
	this.newFormula = newFormula;
	this.positionOfModification = positionOfModification;
    }

    public ConstrainedFormula getNewFormula() {
	return newFormula;
    }

    public ConstrainedFormula getOriginalFormula() {
	return getPositionOfModification ().constrainedFormula ();
    }

    /**
     * @return position within the original formula
     */
    public PosInOccurrence getPositionOfModification() {
	return positionOfModification;
    }

    public String toString () {
	return
	    "Replaced " + positionOfModification +
	    " with " + newFormula;
    }
}
