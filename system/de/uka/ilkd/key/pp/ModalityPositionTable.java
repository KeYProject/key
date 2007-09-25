// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.pp;


/**
 * This is a position table for program modality formaulae.  In
 * addition to the usual tables, it can store a range of character
 * positions for the first statemnt in the java block.
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
