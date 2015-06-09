package org.key_project.jmlediting.core.typechecker;

import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;

public class DefaultTypeChecker implements ITypeChecker {

    @Override
    public ITypeBinding computeType(final IASTNode node) {
        return computeTypeRecursive(node);
    }

    private ITypeBinding computeTypeRecursive(final IASTNode node) {
        
        System.out.println("DefaultTypeChecker.computeTypeRecursive()");
        computeType(node);
        
        return null;
    }
    

}
