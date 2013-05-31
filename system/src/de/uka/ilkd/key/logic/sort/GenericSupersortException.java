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


package de.uka.ilkd.key.logic.sort;

/** this exception is thrown if a generic sort has been declared with
 * an illegal supersort */
public class GenericSupersortException extends Exception {

    /**
     * 
     */
    private static final long serialVersionUID = -5897308261866997061L;
    Sort illegalSort;

    public GenericSupersortException ( String description,
				       Sort   illegalSort ) {
	super(description);
	this.illegalSort = illegalSort;
    }

    public Sort getIllegalSort () {
	return illegalSort;
    }

}
