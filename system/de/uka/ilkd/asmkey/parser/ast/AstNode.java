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


/** Abstract superclass of all AST (abstract syntax tree) classes. All
 *  nodes in the AST contain a reference to their location in the
 *  input stream.
 *
 * @author Hubert Schmid
 */

public abstract class AstNode {

    /** Location of this element in the input file. */
    private final Location location;


    protected AstNode(Location location) {
        this.location = location;
    }


    /** Returns the location of this element in the input file. */
    public final Location getLocation() {
        return location;
    }

}
