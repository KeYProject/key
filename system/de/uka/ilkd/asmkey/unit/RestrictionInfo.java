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

import de.uka.ilkd.key.logic.Name;

/**
 * This class contains import/export information, it means
 * the symbols that are imported/exported directly in the namespace
 * and may be used without prefixing with the module name.
 * We will distinguish 3 states:
 * - NO_SYMBOLS (that is the default)
 * - ALL_SYMBOLS (given by *)
 * - SOME_SYMBOLS (given by a list of names)
 */
public abstract class RestrictionInfo {

    static int NO_SYMBOLS=0;
    static int ALL_SYMBOLS=1;
    static int SOME_SYMBOLS=2;

    private int type;
    private RestrictedSymbol[] symbols;

    RestrictionInfo(int type, RestrictedSymbol[] symbols) {
	this.type = type;
	this.symbols = symbols;
    }

    public boolean isNoSymbols() {
	return type == RestrictionInfo.NO_SYMBOLS;
    }

    public boolean isAllSymbols() {
	return type == RestrictionInfo.ALL_SYMBOLS;
    }

    public boolean isSomeSymbols() { 
	return type == RestrictionInfo.SOME_SYMBOLS;
    }

    protected RestrictedSymbol[] symbols() throws RestrictionInfoException {
	if (isSomeSymbols()) {
	    return symbols;
	} else {
	    throw new RestrictionInfoException();
	}
    }

    protected int type() {
	return type;
    }
    
    public boolean containsSymbol(int type, Name name) throws RestrictionInfoException {
	RestrictedSymbol[] s = symbols();
	boolean result = false;
	
	for(int i=0; !(result) && i<s.length; i++) {
	    result = s[i].type() == type &&
		s[i].symbol().equals(name);
	}
	return result;
    }

}
