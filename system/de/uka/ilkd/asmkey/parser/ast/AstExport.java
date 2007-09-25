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
 * this abstract class is the common ancestor of
 * objects containing export informations.
 */
public abstract class AstExport extends AstNode {
    
    public AstExport (Location location) {
	super(location);
    }

    /** Contrary to import informations, we need only one pass; to be
     * done after parsing all the declaration.
     * @see{AstImport}
     * @see{AstImportVisitor}
     * @see{AstExportVisitor}
     */
    public abstract ExportInfo accept(AstExportVisitor visitor) throws ParserException;
}
