package org.key_project.jmlediting.profile.jmlref.resolver.typecomputer;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.resolver.typecomputer.DefaultTypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.ITypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputerException;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;

/**Computes the types of given IASTNodes
 * 
 * @author Christopher Beckmann
 *
 */
public class JMLTypeComputer extends DefaultTypeComputer implements ITypeComputer{

    public JMLTypeComputer(final ICompilationUnit compilationUnit) {
        super(compilationUnit);
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public ITypeBinding computeType(final IASTNode node) throws TypeComputerException {
                
        System.out.println("JMLTypeComputer.computeStep");
        
        if(node == null) {
            return null;
        }
        
        final int type = node.getType();
                
        //if(type == ExpressionNodeTypes.ARRAY_ACCESS) {}else 
            
        if(type == ExpressionNodeTypes.ARRAY_CLASS) {
            
        } else if(type == ExpressionNodeTypes.ARRAY_DIM_DECL) {
            
        } else if(type == ExpressionNodeTypes.ARRAY_INITIALIZER) {
            
        } else if(type == ExpressionNodeTypes.ASSIGNMENT) {
            
        } else if(type == ExpressionNodeTypes.BINARY_AND 
               || type == ExpressionNodeTypes.BINARY_OR
               || type == ExpressionNodeTypes.BINARY_EXCLUSIVE_OR) {
            
        } else if(type == ExpressionNodeTypes.CAST) {
            try {
                final ResolveResult result = new Resolver().resolve(compilationUnit, node);
            }
            catch (final ResolverException e) {
                // TODO Auto-generated catch block
                e.printStackTrace();
            }
            // TODO .. :D
            
        } else if(type == ExpressionNodeTypes.CONDITIONAL_OP) {
            
        } else if(type == ExpressionNodeTypes.EQUALITY) {
            // the 2 sides must be of the same type
            
        } else if(type == ExpressionNodeTypes.EQUIVALENCE_OP) {
            
        } else if(type == ExpressionNodeTypes.EXPRESSION_LIST) {
            
        //}else if(type == ExpressionNodeTypes.IDENTIFIER) {
            
        } else if(type == ExpressionNodeTypes.IMPLIES) {
            
        } else if(type == ExpressionNodeTypes.JAVA_KEYWORD) {
            // super / this / ?
            
        } else if(type == ExpressionNodeTypes.JML_PRIMARY) {
            // \result \old(...) ?
            
        } else if(type == ExpressionNodeTypes.LOGICAL_AND
               || type == ExpressionNodeTypes.LOGICAL_OR) {
            // & / | / ^ /             
            
        //}else if(type == ExpressionNodeTypes.MEMBER_ACCESS) {
            
        //}else if(type == ExpressionNodeTypes.METHOD_CALL_PARAMETERS) {
            
        } else if(type == ExpressionNodeTypes.MINUS
               || type == ExpressionNodeTypes.PLUS
               || type == ExpressionNodeTypes.MULT) {
            if(node.getChildren().size() < 3) {
                // TODO : Error!
            } 
            for(final IASTNode child : node.getChildren()) {
                // TODO
            }
            
        } else if(type == ExpressionNodeTypes.NEW_EXPRESSION) {
            
        } else if(type == ExpressionNodeTypes.NOT) {
            // !boolean
            
        } else if(type == ExpressionNodeTypes.POST_FIX_EXPR) {
            
        } else if(type == ExpressionNodeTypes.PREFIX_DECREMENT
               || type == ExpressionNodeTypes.PREFIX_INCREMENT) {
            // --int ++int
            
        } else if(type == ExpressionNodeTypes.PRIMARY_EXPR) {
            final IResolver resolver = new Resolver();
            ResolveResult result = null;
            try {
                result = resolver.resolve(compilationUnit, node);
                while(resolver.hasNext()) {
                    result = resolver.next();
                }

            } catch (final ResolverException e) {
                LogUtil.getLogger().logError(e);
                // TODO: could not be resolved.
            } 
            if(result != null) {
                return getTypeFromBinding(result.getBinding());
            }
            
        } else if(type == ExpressionNodeTypes.PRIMITIVE_TYPE) {
            
        } else if(type == ExpressionNodeTypes.REFERENCE_TYPE) {
            
        } else if(type == ExpressionNodeTypes.RELATIONAL_OP) {
            
        } else if(type == ExpressionNodeTypes.SHIFT) {
            
        } else if(type == ExpressionNodeTypes.SUPER_CALL) {
            
        } else if(type == ExpressionNodeTypes.TILDE) {
            
        } else if(type == ExpressionNodeTypes.TYPE_ARGUMENT) {
            
        } else {
            return super.computeType(node);
        }
        throw new TypeComputerException("Can not identify node type.");
    }
        
}
