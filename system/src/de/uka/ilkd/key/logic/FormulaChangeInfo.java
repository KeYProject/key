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



package de.uka.ilkd.key.logic;

/**
 * This class is used to hold information about modified formulas.
 * @see SequentChangeInfo
 */
public class FormulaChangeInfo {
    /** position within the original formula */
    private final PosInOccurrence    positionOfModification;
    /** modified formula */
    private final SequentFormula newFormula;

    public FormulaChangeInfo(PosInOccurrence positionOfModification,
			     SequentFormula newFormula) {
	this.newFormula = newFormula;
	this.positionOfModification = positionOfModification;
    }

    public SequentFormula getNewFormula() {
	return newFormula;
    }

    public SequentFormula getOriginalFormula() {
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
