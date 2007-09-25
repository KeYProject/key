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
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.sort.Sort;


public class SortUnitNamespace extends UnitNamespace {
    
    public SortUnitNamespace(Unit unit) {
	super(unit);
    }

    UnitNamespace getNamespaceForUnit(Unit unit) {
	return unit.sortNS();
    }

    int type() {
	return RestrictedSymbol.SORT;
    }

    private static final String startSymbol(char c) {
	return c=='['?"[":"{";
    }

    private static final String endSymbol(char c) {
	return c=='['?"]":"}";
    }
    
    protected Named lookup_rel(String symbol, Unit unit) {
	/** this is a hack to use the sort {@link Sort.ANY} as it
	 * is linked to no namespace.
	 */
	if (symbol.equals("any")) {
	    return Sort.ANY;
	} else {
	    Matcher m = pattern2.matcher(symbol);
	    Name name;
	    if (m.matches()) {
		char c = symbol.charAt(0);
		name = new Name(startSymbol(c) + unit.name().toString() + "." +
				m.group(1) + endSymbol(c));
	    } else {
		name = new Name(unit.name().toString() + "." + symbol);
	    }
	    return getNamespaceForUnit(unit).lookupLocally(name);
	}
    }

    protected boolean checkSomeSymbol(ImportInfo info, Name name, int type)
	throws RestrictionInfoException {
	Matcher m = pattern2.matcher(name.toString());
	if (m.matches()) {
	    return info.containsSymbol(type, new Name(m.group(1)));
	} else {
	    return info.containsSymbol(type, name);
	}
    }
    
    public Matcher getMatcher(Name name) {
	return pattern.matcher(name.toString());
    }

    /* --- static part ---*/

    private static Pattern pattern = Pattern.compile
	("^(?:[\\[{])?([A-Z][a-zA-Z0-9_#%~]*)\\.[a-zA-Z0-9_#%~]*(?:[\\]}])?$");
    private static Pattern pattern2 = Pattern.compile("^[\\[{]([a-zA-Z0-9_#%~]*)[\\]}]$");

} 
