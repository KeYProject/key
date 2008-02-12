package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;

class SLAttributeResolver extends SLExpressionResolver {

    private static TermBuilder tb = TermBuilder.DF;

    
    public SLAttributeResolver(JavaInfo javaInfo, SLResolverManager manager) {
        super(javaInfo, manager);
    }
    
    protected SLExpression doResolving(SLExpression receiver, String name,
            SLParameters parameters) throws SLTranslationException {

        if (parameters != null) {
            return null;
        }
        Term recTerm = receiver.getTerm();        
        ProgramVariable attribute=null;
        try {
            //try as fully qualified name
            attribute = javaInfo.getAttribute(name);
        } catch(IllegalArgumentException e){
            //try as short name and in enclosing classes
            KeYJavaType containingType = receiver.getKeYJavaType(javaInfo);
            while(attribute==null){
                attribute = javaInfo.lookupVisibleAttribute(name, containingType);
                ProgramVariable et = javaInfo.getAttribute(
                        ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, containingType);
                if(et!=null && attribute==null){
                    containingType = et.getKeYJavaType();
                    if(recTerm!=null){
                        recTerm = tb.dot(recTerm, et);
                    }
                }else{
                    break;
                }
            }
        }
        
        if(attribute != null) {
            if(recTerm == null && !attribute.isStatic()) {
                throw manager.excManager.createException(
                        "Reference to non-static field without receiver: " +
                        attribute.name());
            }
            try {
                Term attributeTerm = tb.dot(recTerm, attribute);
                return manager.createSLExpression(attributeTerm);
            } catch (TermCreationException e) {
                throw manager.excManager.createException(
                        "Wrong attribute reference " + name + ".");
            }
        }   
        
        //try non-rigid heap-dependent function symbol instead of attribute
        Function f = (Function) javaInfo.getServices()
                                        .getNamespaces()
                                        .functions().lookup(new Name(name));
        if(f instanceof NonRigidHeapDependentFunction) {
            if(receiver.isTerm() 
               && f.possibleSubs(new Term[]{receiver.getTerm()})) {
                Term functionTerm = tb.func(f, receiver.getTerm());
                return manager.createSLExpression(functionTerm);                
            } else if(receiver.isType() && f.arity() == 0) {
                Term functionTerm = tb.func(f);
                return manager.createSLExpression(functionTerm);
            }
        }
    
        return null;

    }

    public boolean canHandleReceiver(SLExpression receiver) {
        return receiver != null && (receiver.isTerm() || receiver.isType());
    }

    public boolean needVarDeclaration(String name) {
        return false;
    }

}
