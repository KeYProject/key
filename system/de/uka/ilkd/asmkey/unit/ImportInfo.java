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
 * This class contains import information;
 * more information is given in the parent class
 * {@link RestrictionInfo}
 */
public class ImportInfo extends RestrictionInfo {

    private Unit unit;

    private ImportInfo(Unit unit, int type, RestrictedSymbol[] symbols) {
	super(type, symbols);
	this.unit = unit;
    }
 
    public Unit unit() {
	return unit;
    }

    public static ImportInfo createNoSymbolsImportInfo(Unit unit) {
	return new ImportInfo(unit, RestrictionInfo.NO_SYMBOLS, null);
    }

    public static ImportInfo createAllSymbolsImportInfo(Unit unit) {
	return new ImportInfo(unit, RestrictionInfo.ALL_SYMBOLS, null);
    }

    public static ImportInfo createSomeSymbolsImportInfo(Unit unit, RestrictedSymbol[] symbols) {
	return new ImportInfo(unit, RestrictionInfo.SOME_SYMBOLS, symbols);
    }

    public static ImportInfo createSomeSymbolsImportInfo(Unit unit, RestrictedSymbol symbol) {
	return createSomeSymbolsImportInfo(unit, new RestrictedSymbol[] { symbol });
    }

    public String toString() {
	return "[ImportInfo:unit=" + unit + ";type=" + type() + ";symbols=TODO]"; 
    }

}
