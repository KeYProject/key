// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.NonTerminalProgramElement;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Branch statement.
 *  @author AL
 *  @author <TT>AutoDoc</TT>
 */

public abstract class BranchStatement extends JavaStatement implements NonTerminalProgramElement {

    public BranchStatement() {
	
    }


    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.
     * May contain: Comments
     */ 
    public BranchStatement(ExtList children) {
	super(children);
    }

    /**
     *      Get the number of branches in this container.
     *      @return the number of branches.
     */

    public abstract int getBranchCount();

    /*
      Return the branch at the specified index in this node's
      "virtual" branch array.
      @param index an index for a branch.
      @return the branch with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */

    public abstract Branch getBranchAt(int index);
}
