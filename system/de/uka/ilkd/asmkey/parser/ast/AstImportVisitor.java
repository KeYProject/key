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

import de.uka.ilkd.asmkey.unit.ImportInfo;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;

/**
 * visitor interface for the import ast objects.
 * @see AstImport
 * @author Stanislas Nanchen
 */
public interface AstImportVisitor {
    
    /** visits an import object that does not import symbols */
    ImportInfo visitNoSymbolsImport(Identifier unit, Location location) throws ParserException;

    /** visits an import object that imports all symbols */
    ImportInfo visitAllSymbolsImport(Identifier unit, Location location) throws ParserException;

    /** visits an import object that imports some symbols */
    ImportInfo visitSomeSymbolsImport(Identifier unit, AstRestrictedSymbol[] symbols,
				      Location location)
	throws ParserException;

    /** first visit that only check the name */
    Name visitImportFirstPass(Identifier unit, Location location)throws ParserException;
}
