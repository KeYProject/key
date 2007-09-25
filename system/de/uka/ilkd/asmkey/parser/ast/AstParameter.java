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


/** AstParameter reprensts the declaration of a formal parameter in
 * the definition of named ASM rules.
 *
 * @author Hubert Schmid
 */

public final class AstParameter extends AstNode {

    /** The name of the formal parameter. */
    private final Identifier id;

    /** The sort of the formal parameter. */
    private final AstType sort;


    /** Creates a formal parameter with the given location, name and
     * sort. */
    public AstParameter(Location location, Identifier id, AstType sort) {
        super(location);
        this.id = id;
        this.sort = sort;
    }


    /** Returns the name of the formal parameter. */
    public Identifier getId() {
        return id;
    }

    /** Returns the sort of the formal parameter. */
    public AstType getSort() {
        return sort;
    }

    /** for debug only */
    public String toString() {
        return "[Parameter:id=" + id + ",sort=" + sort + "]";
    }

}
