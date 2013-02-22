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

import de.uka.ilkd.key.java.JavaNonTerminalProgramElement;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.util.ExtList;

/**
 *  Branch.
 *  @author <TT>AutoDoc</TT>
 */

public abstract class BranchImp 
    extends JavaNonTerminalProgramElement implements Branch {

    /**
     * Constructor for the transformation of COMPOST ASTs to KeY.
     * @param children the children of this AST element as KeY classes.    
     * May contain: Comments
     */ 
    public BranchImp(ExtList children) {
	super(children);
    }


    public BranchImp() {
	super();
    }


    public BranchImp(ExtList children, PositionInfo pos) {
        super(children, pos);
    }


}
