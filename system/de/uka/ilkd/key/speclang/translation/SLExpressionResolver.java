package de.uka.ilkd.key.speclang.translation;

import de.uka.ilkd.key.java.JavaInfo;

public abstract class SLExpressionResolver {

    protected final JavaInfo javaInfo;
    protected final SLResolverManager manager;
    
    public SLExpressionResolver(JavaInfo javaInfo, SLResolverManager manager) {
        assert javaInfo != null;
        assert manager  != null;
        
        this.javaInfo = javaInfo;
        this.manager = manager;
    }

    /**
     * Resolves property calls on explicit receivers.
     * @param receiver receiver (may *not* be null)
     * @param name name of the property
     * @param parameters the actual parameters, or null if not applicable
     * @return a suitable term or collection if successful, null otherwise
     * @throws SLTranslationException 
     */
    protected abstract SLExpression doResolving(SLExpression receiver,
                                String name, 
                                SLParameters parameters) throws SLTranslationException;
    
    
    public SLExpression resolve(SLExpression receiver,
                                String name,
                                SLParameters parameters) throws SLTranslationException {
        if (!canHandleReceiver(receiver)) {
            return null;
        }
        return doResolving(receiver, name, parameters);
        
    }
    
    
    protected abstract boolean canHandleReceiver(SLExpression receiver);    
    public abstract boolean needVarDeclaration(String name);
}
