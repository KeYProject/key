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

import de.uka.ilkd.key.logic.ListOfNamed;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;


public abstract class UnitNamespace extends de.uka.ilkd.key.logic.Namespace {

    /** The unit to which the namespace is attacheh */
    protected Unit unit;

    /** Construct an empty Namespace without a parent namespace. */
    public UnitNamespace(Unit unit) {
	super();
	this.unit = unit;
    }
    
    /* namespace part */

    /**
     * With this method, it is possible to retrived an Named object.
     * There are two cases:
     * - the name is full qualified: in this case, it is looked in the
     *   corresponding unit, if it has been imported.
     * - the name is "relative": in this case, it is looked locally and
     *   and then, if not found, looked up in the imported modules according
     *   to the stored import info.
     */
    public Named lookup(Name name) {
	Matcher m = getMatcher(name);
	if (m.matches()) {
	    return lookupFullQualified(m.group(1), name);
	} else {
	    return lookupRelative(name);
	}
    }

    /** for testing */
    Named lookup(String symbol) {
	return lookup(new Name(symbol));
    }

    /**
     * We look for a full qualified Named object, i.e. we know its
     * unit already.
     */
    private Named lookupFullQualified(String unit, Name name) {
	Unit unit_tmp;
	ImportInfo[] imports;
	
	if (this.unit.name().toString().equals(unit)) {
	    return lookupLocally(name);
	} else {
	    imports = this.unit.getImportInfos();
	    for (int i = 0; i<imports.length; i++) {
		unit_tmp = imports[i].unit();
		if (unit_tmp.name().toString().equals(unit)) {
		    return getNamespaceForUnit(unit_tmp).lookupLocally(name);
		}
	    }
	    return null;
	}
    }

    /**
     * We look for a relatively qualified Named object, i.e. we know
     * only the name of the symbol and must use import info to lookup
     * in the imported units.
     */
    private Named lookupRelative(Name name) {
	String symbol = name.toString();
	Named result;
	ImportInfo info;
	ImportInfo[] imports;

	result = lookup_rel(symbol, this.unit);
	if (result == null) {
	    imports = this.unit.getImportInfos();
	    /* we lookup in reverse, as later imports mask 
	     * earlier imports.
	     */
	    for(int i = imports.length-1; i>=0; i--) {
		info = imports[i];
		if (info.isNoSymbols()) {
		    /* the unit does not import directly symbols */
		    continue;
		} else if (info.isAllSymbols()) {
		    /* all the symbol are imported, we can lookup */
		    result = lookup_rel(symbol, info.unit());
		} else { // info.isSomeSymbols() 
		    /* we lookup only if the particular symbol was imported */
		    try {
			if (checkSomeSymbol(info, name, type())) {
			    result = lookup_rel(symbol, info.unit());
			}
		    }
		    catch (RestrictionInfoException e) {
			result = null;
		    }
		}
		if (result != null) {
		    return result;
		}
	    }
	}
	return result;
    }

    /**
     * this methoh looksup the relativelly qualified symbol in the unit
     * by reforming the fully qualified symbol.
     * it is protected as it may be overloaded in case of special symbols
     * like in the {@link SortUnitNamespace}.
     */
    protected Named lookup_rel(String symbol, Unit unit) {
	return getNamespaceForUnit(unit).
	    lookupLocally(new Name(unit.name().toString() + "." + symbol));
    }

    /**
     * this method verifies if a relativelly qualified symbol is imported
     * by an SomeSymbol import info. it is protected as it may be overloaded
     * in the case of special symbols like in the {@link SortUnitNamespace}.
     */
    protected boolean checkSomeSymbol(ImportInfo info, Name name, int type)
	throws RestrictionInfoException {
	return info.containsSymbol(type, name);
    }

    /** this method must be override to get the "correct" namespace
     * form another unit. Examples of such are given in {@link Unit}
     */
    abstract UnitNamespace getNamespaceForUnit(Unit unit);
    
    /**
     * return the type of symbol that this namespace
     * stores. types of symbols are given in the class
     * {@link ImportedSymbol}.
     *
     * @see ImportedSymbol
     */
    abstract int type();

    /** can be overrided to change how the identifier is 
     * patterned, usefull for sortNS, as the sequence sorts
     * have special syntax
     */
    public Matcher getMatcher(Name name) {
	return unitPropMatcher(name);
    }

    protected Named lookupLocally(Name name) {
	return super.lookupLocally(name);
    }

    public static Matcher unitPropMatcher(Name name) {
	return pattern.matcher(name.toString());
    }
    
    /* --- to get all elements --- */

    
    /** as we have no "parent" per se; we must
     * redefined the {@link Namespace#allElements} 
     * method
     */
    public ListOfNamed allElements() {
	ImportInfo[] imports;
	ListOfNamed list = elements();

	imports = this.unit.getImportInfos();
	/* the order of looking up is not important
	 * as we just want the list of all of them.
	 */
	for(int i=0; i<imports.length; i++) {
	    list = list.append(getNamespaceForUnit(imports[i].unit()).elements());
	}

	return list;
    }

    /* --- static part --- */

    /**
     * The following regular expression is used very often,
     * so we set it up statically for reuse
     */
    private static Pattern pattern = Pattern.compile
	("^([A-Z][a-zA-Z0-9_#%~]*)\\.([a-zA-Z0-9_#%~]*)$");

}
