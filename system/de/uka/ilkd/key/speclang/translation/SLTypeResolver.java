package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.recoderext.ImplicitFieldAdder;
import de.uka.ilkd.key.logic.op.ProgramVariable;

class SLTypeResolver extends SLExpressionResolver {

    public SLTypeResolver(JavaInfo javaInfo, SLResolverManager manager) {
        super(javaInfo, manager);
    }

    protected boolean canHandleReceiver(SLExpression receiver) {
        return true;
    }

    protected SLExpression doResolving(SLExpression receiver,
                                       String name,
                                       SLParameters parameters)
                                   throws SLTranslationException {
        try {
            KeYJavaType type = javaInfo.getTypeByClassName(name);
            return manager.createSLExpression(type);
        } catch (RuntimeException e) {
            try{
                if(receiver != null){ 
                    KeYJavaType containingType = receiver.getKeYJavaType(javaInfo);
                    while(true){
                        String typeName = containingType.getSort().name().toString();
                        if(typeName.substring(typeName.lastIndexOf(".")+1).equals(name)){
                            return manager.createSLExpression(containingType);
                        }
                        ProgramVariable et = javaInfo.getAttribute(
                                ImplicitFieldAdder.IMPLICIT_ENCLOSING_THIS, containingType);
                        if(et!=null){
                            containingType = et.getKeYJavaType();
                        }else{
                            break;
                        }
                    }
                }
            }catch(RuntimeException ex){ }
            // Type not found
            return null;
        }
    }

    public boolean needVarDeclaration(String name) {
        return false;
    }

}
