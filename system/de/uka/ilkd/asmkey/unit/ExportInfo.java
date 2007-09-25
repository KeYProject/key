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
 * This class contains export information;
 * more information is given the parent class 
 * {@link RestrictionInfo}.
 */
public class ExportInfo extends RestrictionInfo {

    private ExportInfo(int type, RestrictedSymbol[] symbs) {
	super(type, symbs);
    }

    /* --- static part --- */

    public static ExportInfo createNoSymbolsExportInfo() {
	return new ExportInfo(RestrictionInfo.NO_SYMBOLS, null);
    }

    public static ExportInfo createAllSymbolsExportInfo() {
	return new ExportInfo(RestrictionInfo.ALL_SYMBOLS, null);
    }

    public static ExportInfo createSomeSymbolsExportInfo(RestrictedSymbol[] symbs) {
	return new ExportInfo(RestrictionInfo.SOME_SYMBOLS, symbs);
    }

    public static ExportInfo createSomeSymbolsExportInfo(RestrictedSymbol symbol) {
	return createSomeSymbolsExportInfo(new RestrictedSymbol[] { symbol });
    }

}
