// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class SLMethodResolver extends SLExpressionResolver {

    private TermBuilder tb = TermBuilder.DF;
    
    public SLMethodResolver(JavaInfo javaInfo, 
	    		    SLResolverManager manager,
	    		    KeYJavaType specInClass) {
        super(javaInfo, manager, specInClass);
    }

    protected SLExpression doResolving(SLExpression receiver,
                                       String methodName,
                                       SLParameters parameters)
                                   throws SLTranslationException {

        if(parameters == null || !parameters.isListOfTerm()) {
            return null;
        }

        KeYJavaType containingType = receiver.getKeYJavaType(javaInfo);
        if(containingType == null) {
            return null;
        }
        
        ImmutableList<KeYJavaType> signature = parameters.getSignature(javaInfo.getServices());
        
        ProgramMethod pm = null;
        Term recTerm = receiver.getTerm(); 
        
        
        while(pm==null){
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
                    recTerm = tb.dot(recTerm, et);
                }
            }else{
                break;
            }
        }
        
        if (pm == null)
        {
            return null;
        }
        
        int i;
        Term subs[];
        
        if (!pm.isStatic()) {
            if (!receiver.isTerm()) {
                throw manager.excManager.createException(
                        "non-static method (" + methodName + ") invocation" +
                        " on Type " + receiver.getType());
            }
            subs = new Term[parameters.getParameters().size()+1];
            subs[0] = recTerm;
            i = 1;
        } else {
            subs = new Term[parameters.getParameters().size()];
            i = 0;
        }

        for (SLExpression slExpression : parameters.getParameters()) {
            //Remember: parameters.isLisOfTerm() is true!
            subs[i++] = slExpression.getTerm();
        }
        
        if (pm.getKeYJavaType() == null) {
            // return type is void
            throw manager.excManager.createException("can not use void " +
            		"method \"" + methodName + "\" in specification expression.");
        }
        
        return manager.createSLExpression(tb.func(pm,subs));
    }


    public boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null && (receiver.isTerm() || receiver.isType()) && !receiver.getKeYJavaType(javaInfo).getFullName().endsWith("[]") ;
    }

    public boolean needVarDeclaration(String name) {
        return false;
    }

}
