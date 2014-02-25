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


/**
 * This is a position table for program modality formulae.  In
 * addition to the usual tables, it can store a range of character
 * positions for the first statement in the Java block.
 */

public class ModalityPositionTable extends PositionTable {

    public ModalityPositionTable(int rows) {
	super(rows);
    }

    private Range firstStatementRange = null;
    
    
    public void setFirstStatementRange(Range r){
	firstStatementRange = r;
    }
    
    
    public Range getFirstStatementRange(){
	return new Range(firstStatementRange);
    }
}
