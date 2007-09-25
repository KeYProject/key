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


/** Ast Node for import packages files
 *
 * @author Stanislas Nanchen */

public class AstImportFile extends AstNode {

    /** the path of the file */
    private final String path;
    
    public AstImportFile(Location loc, String path) {
	super(loc);
	this.path = path;
    }

    public final String getPath() {
	return path;
    }

}
