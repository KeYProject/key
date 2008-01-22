package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.ListOfKeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramMethod;

class SLMethodResolver extends SLExpressionResolver {

    private TermBuilder tb = TermBuilder.DF;
    
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
        
        ProgramMethod pm = javaInfo.getProgramMethod(
                containingType,
                methodName,
                signature,
                containingType);
            
        if (pm == null)
        {
            return null;
        }
        
        int i;
        Term subs[];
        
        if (!pm.isStatic()) {
            if (!receiver.isTerm()) {
                throw manager.excManager.createException(
                        "non-static method ( " + methodName + " ) invocation" +
                        " on Type " + receiver.getType());
            }
            subs = new Term[parameters.getParameters().size()+1];
            subs[0] = receiver.getTerm();
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
        
        return manager.createSLExpression(tb.func(pm,subs));
    }


    public boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null && (receiver.isTerm() || receiver.isType()) && !receiver.getKeYJavaType(javaInfo).getFullName().endsWith("[]") ;
    }

    public boolean needVarDeclaration(String name) {
        return false;
    }

}
