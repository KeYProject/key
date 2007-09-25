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
import de.uka.ilkd.key.parser.ParserException;


/** AST node for Taclet Declaration. */

public final class AstTacletDeclaration extends AstSinglePassDeclaration {

    /** The actual taclet. */
    private final AstTaclet taclet;


    public AstTacletDeclaration(Location location, Identifier id, AstTaclet taclet) {
        super(location, id);
        this.taclet = taclet;
    }


    /** Returns the actual taclet. */
    public AstTaclet getTaclet() {
        return taclet;
    }

    /** This methods calls the corresponding method in visitor. */
    public void accept(AstDeclarationVisitor visitor) throws ParserException {
        visitor.visitTaclet(taclet);
    }

    /* inherited */
    public String toString2() {
        return ",taclet=" + taclet;
    }

}
