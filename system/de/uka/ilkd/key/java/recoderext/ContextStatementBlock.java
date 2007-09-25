// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

// This file is taken from the RECODER library, which is protected by the LGPL,
// and modified.

package de.uka.ilkd.key.java.recoderext;

import recoder.java.Statement;
import recoder.java.StatementBlock;
import recoder.list.generic.ASTList;

/**
   Statement block.
   @author AL
   @author <TT>AutoDoc</TT>
 */

public class ContextStatementBlock
    extends StatementBlock implements KeYRecoderExtension{

    private ExecutionContext ec;
        
    /**
     Statement block.
     */
    public ContextStatementBlock() {
    }

    /**
     Statement block.
     */
    public ContextStatementBlock(TypeSVWrapper tr, ExpressionSVWrapper runtime) {
	this(tr != null ? new ExecutionContext(tr, runtime) : null);
    }

    /**
     Statement block.
     */
    public ContextStatementBlock(ExecutionContext ec) {
	this.ec = ec;
    }

    /**
     Statement block.
     @param block a statement mutable list.
     */
    public ContextStatementBlock(TypeSVWrapper tr, ExpressionSVWrapper runtime, 
				 ASTList<Statement> block) {
	super(block);
	if (tr != null) {
	    this.ec = new ExecutionContext(tr, runtime);
	} else {
	    this.ec = null;
	}
    }

    /**
     Statement block.
     @param proto a statement block.
     */

    protected ContextStatementBlock(ContextStatementBlock proto) {
        super(proto);
	this.ec = proto.getExecutionContext();
    }


    public TypeSVWrapper getClassContext() {
	return (TypeSVWrapper)ec.getTypeReference();
    }

    public ExpressionSVWrapper getRuntimeInstance() {
	return (ExpressionSVWrapper)ec.getRuntimeInstance();
    }

    public ExecutionContext getExecutionContext() {
	return ec;
    }

}
