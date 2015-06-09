package org.key_project.jmlediting.profile.jmlref.typechecker;

import java.util.HashMap;
import java.util.Map;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.IBinding;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.typechecker.DefaultTypeChecker;
import org.key_project.jmlediting.core.typechecker.ITypeChecker;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;

/**Computes the types of given IASTNodes
 * 
 * @author Christopher Beckmann
 *
 */
public class TypeChecker extends DefaultTypeChecker implements ITypeChecker {
    
    private final ICompilationUnit compilationUnit;
    
    public TypeChecker(final ICompilationUnit compilationUnit) {
        this.compilationUnit = compilationUnit;
    }
    
    @Override
    public ITypeBinding computeType(final IASTNode node) {
        System.out.println("TypeChecker.computeTypeRecursive()");
        return null;
    }
    
    private ITypeBinding computeTypeRecursive(final IASTNode node) {
        if(node == null) {
            return null;
        }
        
        final int type = node.getType();
        
        if(type == ExpressionNodeTypes.ARRAY_ACCESS) {
            
        }else if(type == ExpressionNodeTypes.ARRAY_CLASS) {
            
        }else if(type == ExpressionNodeTypes.ARRAY_DIM_DECL) {
            
        }else if(type == ExpressionNodeTypes.ARRAY_INITIALIZER) {
            
        }else if(type == ExpressionNodeTypes.ASSIGNMENT) {
            
        }else if(type == ExpressionNodeTypes.BINARY_AND) {
            
        }else if(type == ExpressionNodeTypes.BINARY_EXCLUSIVE_OR) {
            
        }else if(type == ExpressionNodeTypes.BINARY_OR) {
            
        }else if(type == ExpressionNodeTypes.CAST) {
            
        }else if(type == ExpressionNodeTypes.CONDITIONAL_OP) {
            
        }else if(type == ExpressionNodeTypes.EQUALITY) {
            
        }else if(type == ExpressionNodeTypes.EQUIVALENCE_OP) {
            
        }else if(type == ExpressionNodeTypes.EXPRESSION_LIST) {
            
        }else if(type == ExpressionNodeTypes.IDENTIFIER) {
            
        }else if(type == ExpressionNodeTypes.IMPLIES) {
            
        }else if(type == ExpressionNodeTypes.JAVA_KEYWORD) {
            
        }else if(type == ExpressionNodeTypes.JML_PRIMARY) {
            
        }else if(type == ExpressionNodeTypes.LOGICAL_AND) {
            
        }else if(type == ExpressionNodeTypes.LOGICAL_OR) {
            
        }else if(type == ExpressionNodeTypes.MEMBER_ACCESS) {
            
        }else if(type == ExpressionNodeTypes.METHOD_CALL_PARAMETERS) {
            
        }else if(type == ExpressionNodeTypes.MINUS) {
            
        }else if(type == ExpressionNodeTypes.MULT) {
            
        }else if(type == ExpressionNodeTypes.NEW_EXPRESSION) {
            
        }else if(type == ExpressionNodeTypes.NOT) {
            
        }else if(type == ExpressionNodeTypes.PLUS) {
            
        }else if(type == ExpressionNodeTypes.POST_FIX_EXPR) {
            
        }else if(type == ExpressionNodeTypes.PREFIX_DECREMENT) {
            
        }else if(type == ExpressionNodeTypes.PREFIX_INCREMENT) {
            
        }else if(type == ExpressionNodeTypes.PRIMARY_EXPR) {
            
        }else if(type == ExpressionNodeTypes.PRIMITIVE_TYPE) {
            
        }else if(type == ExpressionNodeTypes.REFERENCE_TYPE) {
            
        }else if(type == ExpressionNodeTypes.RELATIONAL_OP) {
            
        }else if(type == ExpressionNodeTypes.SHIFT) {
            
        }else if(type == ExpressionNodeTypes.SUPER_CALL) {
            
        }else if(type == ExpressionNodeTypes.TILDE) {
            
        }else if(type == ExpressionNodeTypes.TYPE_ARGUMENT) {
            
        } else {
            super.computeType(node);
        }
        
        return null;
    }
    
    
    
}
