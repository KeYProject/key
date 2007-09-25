// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.unit;

/**
 * As the list of names of symbols in the ImportInfo
 * class is defined only when the status is SOME_SYMBOLS, we 
 * throw this exception if one attempts to retrieve it otherwise.
 */
public class RestrictionInfoException extends UnitException {

    public RestrictionInfoException() {
	super("You may retrieve the symbols if and only if the predicate isSomeSymbols() is true");
    }

}
