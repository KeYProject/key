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


/** 
 * Represents an exception with position information. The row position is
 * absolut this means, if in a table it is the row of the table, but the column
 * position is relative to the text and does not describe the column of the
 * table. (has to be changed)
 */
public abstract class SVInstantiationExceptionWithPosition 
    extends SVInstantiationException {

    /**
     * 
     */
    private static final long serialVersionUID = 2157800633859913303L;
    private int row;
    private int column;
    private boolean inIfSequent;
         
    public SVInstantiationExceptionWithPosition( String description, 
						 int    row, 
						 int    column,
						 boolean inIfSequent ) {
	super(description);
	this.row    = row;
	this.column = column;
	this.inIfSequent = inIfSequent;

    }
    
    public boolean inIfSequent() {
	return inIfSequent;
    }

    public int getRow() {
	return row;
    }

    public int getColumn() {
	return column;
    }

    public String getMessage () {
	String errmsg = super.getMessage() + ":";
	if ( inIfSequent() ) {
	    errmsg += row <= 0 ? "" : ("\nAssumption number:" + row);
	} else {
	    errmsg += row    <= 0 ? "" : ("\nRow: " + getRow());
	    errmsg += column <= 0 ? "" : ("\nColumn: " + getColumn());	
	}
	return errmsg;
    }    

    /**
     * Returns a string representation of this exception.
     */
    public String toString() {
	return getMessage();
    }
}
