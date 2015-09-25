package org.key_project.jmlediting.core.resolver;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IStringNode;

public class ResolveResult {
    
    private final ASTNode jdtNode;
    private final ResolveResultType type;
    private final IBinding binding;
    private final IStringNode stringNode;
    
    public ResolveResult(final ASTNode jdtNode, final ResolveResultType type, final IBinding binding, final IStringNode stringNode) {
        this.jdtNode = jdtNode;
        this.type = type;
        this.binding = binding;
        this.stringNode = stringNode;
    }

    /**
     * Get the binding of the result.
     * @return the {@link IBinding} for the stored result
     */
    public final IBinding getBinding() {
        return binding;
    }
    
    /**
     * Get the {@link ASTNode} of the result.
     * @return the {@link ASTNode} for the stored result
     */
    public final ASTNode getJDTNode() {
        return jdtNode;
    }

    public final String getName() {
        return stringNode.getString();
    }

    public final ResolveResultType getResolveType() {
        return type;
    }
    
    public final IStringNode getStringNode() {
        return stringNode;
    }
    
    /** Get the return type.
     * @return the return type of the Method. If the stored resolve information is not from a method, it returns null;
     */
    public final ITypeBinding getMethodReturnType() {
        if(type == ResolveResultType.METHOD) {
            return ((IMethodBinding) binding).getReturnType();
        }
        return null;
    }
}
