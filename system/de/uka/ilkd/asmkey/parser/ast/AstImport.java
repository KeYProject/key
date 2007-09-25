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

import de.uka.ilkd.asmkey.unit.AbstractUnitParser;
import de.uka.ilkd.asmkey.unit.ImportInfo;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;

/**
 * this abstract class is the common ancestor of
 * objects containing import informations.
 */
public abstract class AstImport extends AstNode {
    
    protected Name name = null;
    
    public AstImport (Location location) {
	super(location);
    }

    /** This methods calls the intern parsing method that does the actual
     * work and stores the parsed name.
     */
    public Name acceptFirstPass(AstImportVisitor visitor) throws ParserException {
	name = internAcceptFirstPass(visitor);
	return name;
    }

    /** This methods calls the corresponding method in visitor.
     * the first pass simply check that the imported unit really exists.
     */
    protected abstract Name internAcceptFirstPass(AstImportVisitor visitor) throws ParserException;

    /** This methods calls the corresponding method in visitor.
     * the second pass is there only the someSymbol importing and 
     * checks whether all imported symbols really exists.
     */
    public abstract ImportInfo acceptSecondPass(AstImportVisitor visitor) throws ParserException;


    /**
     * after the first pass, the name is stored for later use.
     * @see #acceptFirstPass
     * @see AbstractUnitParser#parse
     */
    public Name name() throws ParserException {
	if (name == null) {
	    throw new ParserException("AstImport:name has not been parsed", getLocation());
	} else {
	    return name;
	}
    }
}
