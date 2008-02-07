package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;

class SLTypeResolver extends SLExpressionResolver {

    public SLTypeResolver(JavaInfo javaInfo, SLResolverManager manager) {
        super(javaInfo, manager);
    }

    protected boolean canHandleReceiver(SLExpression receiver) {
        return receiver == null;
    }

    protected SLExpression doResolving(SLExpression receiver,
                                       String name,
                                       SLParameters parameters)
                                   throws SLTranslationException {

        try {
            KeYJavaType type = javaInfo.getTypeByClassName(name);
            return manager.createSLExpression(type);
        } catch (RuntimeException e) {
            // Type not found
            return null;
        }
    }

    public boolean needVarDeclaration(String name) {
        return false;
    }

}
