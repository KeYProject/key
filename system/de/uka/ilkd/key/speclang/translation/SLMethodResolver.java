// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.translation;

import java.util.Iterator;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;


public final class SLMethodResolver extends SLExpressionResolver {
  
    public SLMethodResolver(JavaInfo javaInfo, SLResolverManager manager) {
        super(javaInfo, manager);
    }

    
    @Override
    protected SLExpression doResolving(SLExpression receiver,
                                       String methodName,
                                       SLParameters parameters)
                                   throws SLTranslationException {

        if(parameters == null || !parameters.isImmutableListOfTerm()) {
            return null;
        }

        KeYJavaType containingType = receiver.getType();
        if(containingType == null) {
            return null;
        }
        
        ImmutableList<KeYJavaType> signature = parameters.getSignature(javaInfo.getServices());
        
        ProgramMethod pm = null;
        Term recTerm = receiver.getTerm(); 
        
        
        while(pm == null) {
            pm = javaInfo.getProgramMethod(
                    containingType,
                    methodName,
                    signature,
                    containingType);
            ProgramVariable et = javaInfo.getAttribute(
                    ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, containingType);
            if(et!=null && pm==null){
                containingType = et.getKeYJavaType();
                if(recTerm!=null){
                    final Function fieldSymbol 
                    	= services.getTypeConverter().getHeapLDT().getFieldSymbolForPV(et, services);
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
            subs[0] = recTerm;
            subs[1] = TB.heap(services);            
            i = 2;
        } else {
            subs = new Term[parameters.getParameters().size() + 1];
            subs[0] = TB.heap(services);
            i = 1;
        }
        
        Iterator<SLExpression> it = parameters.getParameters().iterator();
        while(it.hasNext()) {
            //Remember: parameters.isLisOfTerm() is true!
            subs[i++] = it.next().getTerm();
        }
        
        if (pm.getKeYJavaType() == null) {
            // return type is void
            throw manager.excManager.createException("can not use void " +
            		"method \"" + methodName + "\" in specification expression.");
        }
        
        return new SLExpression(TB.tf().createTerm(pm, subs), 
        	                pm.getKeYJavaType());
    }


    @Override    
    public boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null 
               && !receiver.getType().getFullName().endsWith("[]");
    }

    
    @Override    
    public boolean needVarDeclaration(String name) {
        return false;
    }
}
