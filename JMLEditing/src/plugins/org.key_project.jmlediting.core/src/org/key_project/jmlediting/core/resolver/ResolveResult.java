package org.key_project.jmlediting.core.resolver;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;

public class ResolveResult {
    
    private ASTNode jdtNode = null;
    private ResolveResultType type = ResolveResultType.UNSPECIFIED;
    private IBinding binding = null;
    
    public ResolveResult(ASTNode jdtNode, ResolveResultType type, IBinding binding) {
        this.jdtNode = jdtNode;
        this.type = type;
        this.binding = binding;
    }

    public IBinding getBinding() {
        return binding;
    }
    
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
