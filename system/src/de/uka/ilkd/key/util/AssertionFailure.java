// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

/** this exception is shown if an assertion has failed */
package de.uka.ilkd.key.util;

public class AssertionFailure extends RuntimeException {


    public AssertionFailure() {
	super();
    }

    public AssertionFailure(String msg) {
	super(msg);
    }



}
