// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

// This file is taken from the RECODER library, which is protected by the LGPL,
// and modified.

package de.uka.ilkd.key.java.recoderext;

import recoder.java.StatementBlock;

/**
   Statement block.
   @author AL
   @author <TT>AutoDoc</TT>
 */

public class ContextStatementBlock
    extends StatementBlock implements KeYRecoderExtension{

    /**
     * 
     */
    private static final long serialVersionUID = -7812560435975572578L;
    private ExecutionContext ec;
        
    /**
     Statement block.
     */
    public ContextStatementBlock() {
    }

    /**
     Statement block.
     */
    public ContextStatementBlock(TypeSVWrapper tr, MethodSignatureSVWrapper pm, ExpressionSVWrapper runtime) {
	this(tr != null ? new ExecutionContext(tr, pm, runtime) : null);
    }

    /**
     Statement block.
     */
    public ContextStatementBlock(ExecutionContext ec) {
	this.ec = ec;
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