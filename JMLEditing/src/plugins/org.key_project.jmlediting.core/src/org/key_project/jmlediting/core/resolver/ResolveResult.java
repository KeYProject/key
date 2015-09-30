package org.key_project.jmlediting.core.resolver;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IStringNode;

/**
 * A container for information about the resolve result.
 * 
 * @author Christopher Beckmann
 *
 */
public class ResolveResult {
    
    private final ASTNode jdtNode;
    private final ResolveResultType type;
    private final IBinding binding;
    private final IStringNode stringNode;
    private final ITypeBinding returnValue;
    
    /**
     * Creates a ResolveResult with the given values.
     * @param jdtNode the {@link ASTNode} of the result
     * @param type the {@link ResolveResultType} of the result 
     * @param binding the {@link IBinding} to the declaration of the result
     * @param returnValue the {@link ITypeBinding} to the type we would perform a member access search on
     * @param stringNode the {@link IStringNode} that was used to find the result
     */
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

    /** Gets the name from the {@link IStringNode} that is saved.
     * 
     * @return the name of the result
     */
    public final String getName() {
        return stringNode.getString();
    }

    /** Gets the {@link ResolveResultType} saved in this ResolveResult.
     * 
     * @return the {@link ResolveResultType} of the result
     */
    public final ResolveResultType getResolveType() {
        return type;
    }
    
    /** Gets the {@link IStringNode} saved.
     * 
     * @return the {@link IStringNode} of the result. Can be {@code null} if the ResolveResult was built using another {@link IASTNode} instead.
     */
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
