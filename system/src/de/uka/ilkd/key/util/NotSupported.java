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


package de.uka.ilkd.key.util;
/** this exception is thrown if a feature is not implemented in this version */

public class NotSupported extends RuntimeException {

    /**
     * 
     */
    private static final long serialVersionUID = -1804357960867777191L;

    public NotSupported(String msg) {
	super(msg);
    }

}
