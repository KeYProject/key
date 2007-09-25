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

import de.uka.ilkd.asmkey.unit.ExportInfo;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;

/**
 * visitor interface for the export ast objects.
 * @see AstExport
 * @author Stanislas Nanchen
 */
public interface AstExportVisitor {
    
    /** visits an export object that does not export symbols */
    ExportInfo visitNoSymbolsExport() throws ParserException;

    /** visits an export object that exports all symbols */
    ExportInfo visitAllSymbolsExport(Location location) throws ParserException;

    /** visits an export object that exports some symbols */
    ExportInfo visitSomeSymbolsExport(AstRestrictedSymbol[] symbols,
				      Location location)
	throws ParserException;
}
