package org.key_project.jmlediting.core.resolver;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;

public class ResolveResult {
    
    private final ASTNode jdtNode;
    private final ResolveResultType type;
    private final IBinding binding;
    
    public ResolveResult(final ASTNode jdtNode, final ResolveResultType type, final IBinding binding) {
        this.jdtNode = jdtNode;
        this.type = type;
        this.binding = binding;
    }

    /**
     * Get the binding of the result.
     * @return the {@link IBinding} for the stored result
     */
    public IBinding getBinding() {
        return binding;
    }
    
    /**
     * Get the {@link ASTNode} of the result.
     * @return the {@link ASTNode} for the stored result
     */
    public ASTNode getJDTNode() {
        return jdtNode;
    }

    public String getName() {
        return binding.getName();
    }

    public ResolveResultType getResolveType() {
        return type;
    }
    
    /** Get the return type.
     * @return the return type of the Method. If the stored resolve information is not from a method, it returns null;
     */
    public ITypeBinding getMethodReturnType() {
        if(type == ResolveResultType.METHOD) {
            return ((IMethodBinding) binding).getReturnType();
        }
        return null;
    }
}
