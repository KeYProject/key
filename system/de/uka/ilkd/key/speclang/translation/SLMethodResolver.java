// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.explicitheap.ExplicitHeapConverter;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;

public class SLMethodResolver extends SLExpressionResolver {
  
    public SLMethodResolver(JavaInfo javaInfo, SLResolverManager manager) {
        super(javaInfo, manager);
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
        
        ListOfKeYJavaType signature = parameters.getSignature(javaInfo.getServices());
        
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
                    final Function fieldSymbol = ExplicitHeapConverter.INSTANCE.getFieldSymbol(et, services);
                    recTerm = TB.dot(services, et.sort(), recTerm, fieldSymbol);
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
        
        IteratorOfSLExpression it = parameters.getParameters().iterator();
        while(it.hasNext()) {
            //Remember: parameters.isLisOfTerm() is true!
            subs[i++] = it.next().getTerm();
        }
        
        if (pm.getKeYJavaType() == null) {
            // return type is void
            throw manager.excManager.createException("can not use void " +
            		"method \"" + methodName + "\" in specification expression.");
        }
        
        return manager.createSLExpression(TB.func(pm,subs));
    }


    public boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null && (receiver.isTerm() || receiver.isType()) && !receiver.getKeYJavaType(javaInfo).getFullName().endsWith("[]") ;
    }

    public boolean needVarDeclaration(String name) {
        return false;
    }

}
