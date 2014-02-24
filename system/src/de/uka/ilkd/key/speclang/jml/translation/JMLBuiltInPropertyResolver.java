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


package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.speclang.translation.SLExpression;
import de.uka.ilkd.key.speclang.translation.SLExpressionResolver;
import de.uka.ilkd.key.speclang.translation.SLParameters;
import de.uka.ilkd.key.speclang.translation.SLResolverManager;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 * Resolver for built-in JML operators. Currently only handles array length.
 */
public final class JMLBuiltInPropertyResolver extends SLExpressionResolver {
    
    private final SeqLDT seqLDT;

    
    public JMLBuiltInPropertyResolver(JavaInfo javaInfo, 
	    			      SLResolverManager manager,
	    			      KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
        this.seqLDT = services.getTypeConverter().getSeqLDT();
    }
    

    @Override
    protected boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null;
    }    
    
    
    @Override
    protected SLExpression doResolving(SLExpression receiver, 
	    			       String name,
	    			       SLParameters parameters) 
    		throws SLTranslationException {
        if(parameters != null) {
            return null;
        }
        
        if(name.equals("length") 
           && receiver.isTerm() 
           && receiver.getTerm().sort().equals(seqLDT.targetSort())) {
            return new SLExpression(services.getTermBuilder().seqLen(receiver.getTerm()),
        	                    javaInfo.getPrimitiveKeYJavaType(PrimitiveType.JAVA_INT));
        }
    
        return null;
    }
}
