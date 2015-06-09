package org.key_project.jmlediting.core.typechecker;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;

public interface ITypeComputeFunction {
    
    /**Gets the type of the expression.
     * @param node the {@link IASTNode} that represents the expression to be checked
     * @return the {@link ITypeBinding} that is the result of the given {@link IASTNode} expression
     */
    public ITypeBinding computeType(final IASTNode node);
}
