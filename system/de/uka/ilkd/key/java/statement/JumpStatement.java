// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.statement;

/**
 *  Jump statement.
 *  @author <TT>AutoDoc</TT>
 */
public abstract class JumpStatement extends JavaStatement {

    /**
     *      Jump statement.
     * @param children the children of this AST element as KeY classes.
     * May contain: Comments
     */
    public JumpStatement(de.uka.ilkd.key.util.ExtList children) {
	super(children);
    }


    /**
     *      Jump statement.
     */
    public JumpStatement() {
    }

}
