// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//


package de.uka.ilkd.asmkey.unit;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

import de.uka.ilkd.key.logic.Name;

/**
 * for functions, needed to import easily the timedfunctions
 * without having to precise in the import for the some symbol
 * import.
 */
public class FunctionUnitNamespace extends UnitNamespace {

    public FunctionUnitNamespace(Unit unit) {
	super(unit);
    }

    UnitNamespace getNamespaceForUnit(Unit unit) {
	return unit.funcNS();
    }
    
    int type() {
	return RestrictedSymbol.FUNCTION;
    }

    protected boolean checkSomeSymbol(ImportInfo info, Name name, int type)
    throws RestrictionInfoException {
	Matcher m = pattern.matcher(name.toString());
	if (m.matches()) {
	    return info.containsSymbol(type, new Name(m.group(1)));
	} else {
	    return info.containsSymbol(type, name);
	}
    }


    private static Pattern pattern = Pattern.compile("^([a-zA-Z0-9_#%~]*)_$");
}
