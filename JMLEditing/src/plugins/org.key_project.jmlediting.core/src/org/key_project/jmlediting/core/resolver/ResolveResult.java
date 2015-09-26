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
    private final ITypeBinding returnValue;
    
    public ResolveResult(final ASTNode jdtNode, final ResolveResultType type, final IBinding binding, final ITypeBinding returnValue, final IStringNode stringNode) {
        this.jdtNode = jdtNode;
        this.type = type;
        this.binding = binding;
        this.stringNode = stringNode;
        this.returnValue = returnValue;
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
    
    /** Gets the return type if this ResolveResult stores a method.
     *  Or if the type of whatever is stored in here is parameterized, 
     *  it will return the type it should actually be.
     * 
     * @return an {@link ITypeBinding}.
     */
    public final ITypeBinding getReturnType() {
        return returnValue;
    }
}
