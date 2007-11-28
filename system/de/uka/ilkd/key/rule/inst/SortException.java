// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.inst;

/** this exception is thrown from an "SVInstantiations"-Object if the
 * sorts of a schema variable and its instantiation are not compatible
 * (and not generic) */
public class SortException extends IllegalInstantiationException {

    public SortException(String description) {
	super(description);
    } 


}
