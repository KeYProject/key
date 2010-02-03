// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
/**
 * This class encapsulates initializers of a for loop
 */

package de.uka.ilkd.key.java.statement;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.util.ExtList;

public class LoopInit extends JavaNonTerminalProgramElement
    implements StatementContainer, ILoopInit{

    ArrayOfLoopInitializer inits;

    public LoopInit(ArrayOfLoopInitializer exprarr) {
	inits = exprarr;
    }

    public LoopInit(LoopInitializer[] exprarr) {
	inits = new ArrayOfLoopInitializer(exprarr);
    }

    public LoopInit(ExtList ups, PositionInfo pos) {
        super(pos);
	final LoopInitializer[] exps = new LoopInitializer[ups.size()];	
	for (int i=0; i<exps.length; i++) {
	    exps[i] = (LoopInitializer)ups.get(i);
	}
	inits = new ArrayOfLoopInitializer(exps);
    }
    

    /**
     *      Get the number of statements in this container.
     *      @return the number of statements.
     */
    public int getStatementCount() {
	return inits.size();
    }

    /*
      Return the statement at the specified index in this node's
      "virtual" statement array.
      @param index an index for an statement.
      @return the statement with the given index.
      @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
      of bounds.
    */
    public Statement getStatementAt(int index) {
	return inits.getLoopInitializer(index);
    }

    public int size() {
	return getStatementCount();
    }

    public ArrayOfLoopInitializer getInits() {
	return inits;
    }
    
    public void visit(Visitor v) {
	v.performActionOnLoopInit(this);
    }

    public int getChildCount() {
	return getStatementCount();
    }

    public ProgramElement getChildAt(int index) {
	return getStatementAt(index);
    }

}
