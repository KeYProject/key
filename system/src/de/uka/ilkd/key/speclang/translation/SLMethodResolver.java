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


package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;

/**
 * Resolver for method calls in specifications.
 */
public final class SLMethodResolver extends SLExpressionResolver {
  
    public SLMethodResolver(JavaInfo javaInfo, 
	    		    SLResolverManager manager,
	    		    KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
    }
    

    @Override    
    protected boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null 
               && !receiver.getType().getFullName().endsWith("[]");
    }
    
    
    @Override
    protected SLExpression doResolving(SLExpression receiver,
                                       String methodName,
                                       SLParameters parameters)
                                   throws SLTranslationException {

        if(parameters == null || !parameters.isListOfTerm()) {
            return null;
        }

        KeYJavaType containingType = receiver.getType();
        if(containingType == null) {
            return null;
        }
        
        ImmutableList<KeYJavaType> signature = parameters.getSignature(javaInfo.getServices());
        
        IProgramMethod pm = null;
        Term recTerm = receiver.getTerm(); 
        
        
        while (true) {
            pm = javaInfo.getToplevelPM(containingType, methodName, signature);
            LocationVariable et = (LocationVariable) javaInfo.getAttribute(
                    ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, containingType);
            if(et!=null && pm==null){
                containingType = et.getKeYJavaType();
                if(recTerm!=null){
                    final Function fieldSymbol 
                    	= services.getTypeConverter()
                    	          .getHeapLDT()
                    	          .getFieldSymbolForPV(et, services);
                    recTerm = TB.dot(services, et.sort(), recTerm, fieldSymbol);
                }
            }else{
                break;
            }
        }
        
        if(pm == null) {
            return null;
        }
        
        int i;
        Term[] subs;
        
        if(!pm.isStatic()) {
            if (!receiver.isTerm()) {
                throw manager.excManager.createException(
                        "non-static method (" + methodName + ") invocation" +
                        " on Type " + receiver.getType());
            }
            subs = new Term[parameters.getParameters().size() + 2];
            subs[0] = TB.getBaseHeap(services);
            subs[1] = recTerm;
            i = 2;
        } else {
            subs = new Term[parameters.getParameters().size() + 1];
            subs[0] = TB.getBaseHeap(services);
            i = 1;
        }

        for (SLExpression slExpression : parameters.getParameters()) {
            //Remember: parameters.isLisOfTerm() is true!
            subs[i++] = slExpression.getTerm();
        }
        
        if (pm.isVoid()) {
            throw manager.excManager.createException("can not use void " +
            		"method \"" + methodName + "\" in specification expression.");
        }
        
        return new SLExpression(TB.tf().createTerm(pm, subs), 
        	                pm.getReturnType());
    }

}
