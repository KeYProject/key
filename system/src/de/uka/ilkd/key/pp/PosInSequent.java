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


package de.uka.ilkd.key.pp;

import de.uka.ilkd.key.logic.PosInOccurrence;

/**
 * describes a position in a sequent including the bounds within a string
 * representation of the sequent. In contrast to PosInOccurrence and
 * PosInTerm of package de.uka.ilkd.key.logic, this class is mutable,
 * i.e the bounds may be set later in an already existing PosInSequent
 * instance. Apart from the bounds, PosInSequent has the following kind
 * of states: It marks the whole sequent, the whole antecedent, the whole
 * succedent or includes a PosInOccurrence if a position within a
 * constrained formula of the sequent is referred to. In the latter case
 * it contains also information whether the whole constrained formula
 * is referred to or the formula or the constraint.
 */
public class PosInSequent {

    private Range bounds;
    private boolean sequent;
    private PosInOccurrence posInOcc=null;

    private Range firstJavaStatementRange = null;
    /**
     * creates a PosInSequent that points to the whole sequent.
     */
    public static PosInSequent createSequentPos() {
	return new PosInSequent(null, true);
    }

    /**
     * creates a PosInSequent that points to a SequentFormula described by
     * a PosInOccurrence. Additionally a boolean indicates whether the
     * the whole SequentFormula or just the formula is meant.
     * @param posInOcc the PositionInOccurrence describing the
     * SequentFormula and maybe a subterm of its formula.
     */
    public static PosInSequent createCfmaPos(PosInOccurrence posInOcc) {
	return new PosInSequent(posInOcc, false);
    }


    // use the create... above for getting instances of PosInSequent
    private PosInSequent(PosInOccurrence posInOcc, 
			 boolean sequent  ){
	this.posInOcc=posInOcc;
	this.sequent=sequent;
    }


    /**
     * sets the bounds, i.e. the start and end positions 
     * of the PosInSequent
     * in a string representation of a sequent.
     * @param r the range of character positions
     */
    public void setBounds(Range r) {
	bounds = r;
    }


    /**
     * returns the bounds in a string representation of a sequent
     * @return start position
     */
    public Range getBounds() {
	return bounds;
    }

    /**
     * sets the bounds, i.e. the start and end positions of the first
     * Java statement, of a corresponding Java program in a string
     * representation of the sequent.
     * @param r the range for the first statement in the corresponding program
     */
    public void setFirstJavaStatementRange(Range r) {
	firstJavaStatementRange = r;
    }

    /**
     * returns the bounds, i.e. the start and end positions of the first Java statement, 
     * of a corresponding Java program in a string representation of the sequent.
     * @return the range specifying the first statement in the corresponding program
     */
    public Range getFirstJavaStatementRange() {
	return firstJavaStatementRange;
    }
    

    /**
     * returns the PosInOccurrence if the PosInSequent marks a
     * SequentFormula or parts of it, null otherwise.
     */	
    public PosInOccurrence getPosInOccurrence() {
	return posInOcc;
    }
		
    /**
     * returns true if the PosInSequent points to a whole Sequent
     */
    public boolean isSequent() {
	return sequent;
    }

    /**
     * returns a string representation of this PosInSequent
     */
    public String toString() {
	if (isSequent()) return "Whole Sequent";
	return ""+posInOcc;
    }
}

