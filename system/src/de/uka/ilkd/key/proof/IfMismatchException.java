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

/** this exception thrown if an if-sequent match failed */
public class IfMismatchException extends SVInstantiationException {

    /**
     * 
     */
    private static final long serialVersionUID = 933425921270034135L;

    public IfMismatchException(String description) {
	super(description);
    } 


}
