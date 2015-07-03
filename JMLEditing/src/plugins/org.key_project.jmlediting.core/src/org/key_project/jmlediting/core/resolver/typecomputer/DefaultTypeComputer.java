package org.key_project.jmlediting.core.resolver.typecomputer;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.IMethodBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.IVariableBinding;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;

public class DefaultTypeComputer implements ITypeComputer {

    protected ICompilationUnit compilationUnit;

    public DefaultTypeComputer(final ICompilationUnit compilationUnit) {
        this.compilationUnit = compilationUnit;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ITypeBinding computeType(final IASTNode node) throws TypeComputerException {
        
        System.out.println("DefaultTypeComputer.computeStep");
        
        if(node == null) {
            return null;
        }
        
        if(node.getType() == NodeTypes.STRING) {
            // end
        } else if(node.getType() == NodeTypes.KEYWORD) {
            // TODO: check childs
            
        } else if(node.getType() == NodeTypes.KEYWORD_APPL) {
            
        } else if(node.getType() == NodeTypes.KEYWORD_CONTENT) {
            
        } else if(node.getType() == NodeTypes.NODE) {
            
        } else if(node.getType() == NodeTypes.LIST) {
            
        } else if(node.getType() == NodeTypes.SEQ) {
            
        } else if(node.getType() == NodeTypes.SOME) {
            
        } else if(node.getType() == NodeTypes.NONE) {
            
        }
        throw new TypeComputerException("Can not identify the node type.");
    }
    
    
    public static ITypeBinding getTypeFromBinding(final IBinding binding) {
        if(binding instanceof IVariableBinding) {
            return ((IVariableBinding) binding).getType();
        } else if(binding instanceof IMethodBinding) {
            return ((IMethodBinding) binding).getReturnType();
        } else if(binding instanceof ITypeBinding) {
            return (ITypeBinding) binding;
        }
        return null;
    }

    public static boolean typeMatch(final ITypeBinding b1, final ITypeBinding b2) {
        // TODO: check if the first owns the second or something..
        //
        // ITypeBinding - isCastCompatible(type); ! :D
        //b1.isCastCompatible(b2);
        
        return b1.isEqualTo(b2);
    }
}
