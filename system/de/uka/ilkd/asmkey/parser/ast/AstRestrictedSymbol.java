// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.ast;

import de.uka.ilkd.key.parser.Location;

/**
 * this abstract class is the common ancestor of
 * objects containing imported symbols informations; 
 * for the SomeSymbol import.
 */
public class AstRestrictedSymbol extends AstNode {

    public static final int META_OPERATOR=0;
    public static final int SORT=1;
    public static final int SCHEMA_VARIABLE=2;
    public static final int FUNCTION=3;
    public static final int ASMRULE=5;
    public static final int TACLET=6;
    public static final int PROPOSITION=7;

    private int type;
    private Identifier symbol;

    public AstRestrictedSymbol(Location location, int type, Identifier symbol) {
	super(location);
	this.type = type;
	this.symbol = symbol;
    }

    public int type() {
	return type;
    }

    public Identifier symbol() {
	return symbol;
    }

}
