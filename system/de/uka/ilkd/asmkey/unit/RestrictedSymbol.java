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
 * this class contains imported and exported symbols informations; 
 * for the SomeSymbol import and export.
 * @see{RestrictionInfo}
 * @see{ExportInfo}
 * @see{ImportInfo}
 */
public class RestrictedSymbol {

    public static final int META_OPERATOR=0;
    public static final int SORT=1;
    public static final int SCHEMA_VARIABLE=2;
    public static final int FUNCTION=3;
    public static final int ASMRULE=5;
    public static final int TACLET=6;
    public static final int PROPOSITION=7;
    public static final int HEURISTIC=8;

    private int type;
    private Name symbol;

    public RestrictedSymbol(int type, String symbol) {
	this(type, new Name(symbol));
    }

    public RestrictedSymbol(int type, Name symbol) {
	this.type = type;
	this.symbol = symbol;
    }

    public int type() {
	return type;
    }

    public Name symbol() {
	return symbol;
    }


    /* --- static part --- */

    public static String getStringForType(int type) {
	switch(type) {
	case META_OPERATOR:
	    return "MetaOperator";
	case SORT:
	    return "Sort";
	case SCHEMA_VARIABLE:
	    return "SchemaVariable";
	case FUNCTION:
	    return "Function";
	case ASMRULE:
	    return "Asm";
	case TACLET:
	    return "Taclet";
	case PROPOSITION:
	    return "Proposition";
	case HEURISTIC:
	    return "Heuristic";
	}
	return "";
    }

}
