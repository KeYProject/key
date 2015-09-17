package org.key_project.jmlediting.profile.jmlref.resolver.typecomputer;

import java.lang.reflect.Array;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.Scope;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.util.JavaBasicsNodeTypes;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.ITypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputerException;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.util.jdt.JDTUtil;

/** Computes the types of given {@link IASTNodes}.
 * 
 * @author Christopher Beckmann
 *
 */
public class JMLTypeComputer extends TypeComputer implements ITypeComputer {

    public JMLTypeComputer(final ICompilationUnit compilationUnit) {
        super(compilationUnit);
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public ITypeBinding computeType(final IASTNode node) throws TypeComputerException {
        
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

            // TODO: call on child? .. give everything to resolver?
            // compare afterwards?
           
           // If type is primitive Type .. TypeComputer has to handle it.
           // TODO: How is the Cast tree built? Return 1st Child?
           return computeType(node.getChildren().get(0));
           
           //return callResolver(toResolve, new Resolver());
            
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
            // types should be boolean
            if(node.getChildren().size() < 3) {
                //TODO: Error erstellen throw new TypeComputerException("Can not have a logical operator without two operands.", node);
            }
            else return createWellKnownType("boolean");
            
        } else if(type == ExpressionNodeTypes.MINUS
               || type == ExpressionNodeTypes.PLUS
               || type == ExpressionNodeTypes.MULT) {
            if(node.getChildren().size() % 2 != 1 || node.getChildren().size() == 1) {
               return null;
            //TODO: Error erstellen throw new TypeComputerException("Arythmetic operation ecpects a sceond operand", node);
            }
            ITypeBinding operand;
            ITypeBinding savedType = CHAR;
            for(final IASTNode child : node.getChildren()) {
                if(child.getType() != NodeTypes.STRING) {
                    operand = computeType(child);
                    if (arithmeticalBinding(operand)) {
                       if(operand.equals(FLOAT) || operand.equals(P_FLOAT)) {
                          savedType = FLOAT;
                       } else if(operand.equals(INTEGER) || operand.equals(P_INTEGER)) {
                          if(!operand.equals(FLOAT)) {
                             savedType = INTEGER;
                          }
                       }
                    } else {
                       return null; // TODO: Create Error
                    }
                }
            }
            return savedType;
            
            
            
        } else if(type == ExpressionNodeTypes.NEW_EXPRESSION) {
            
        } else if(type == ExpressionNodeTypes.NOT) {
            // !boolean
            if(node.getChildren().size() != 1) {
                throw new TypeComputerException("This node's child count should be one.", node);
            }
            
            final ITypeBinding expected = createWellKnownType("boolean");
            final ITypeBinding actual = computeType(node.getChildren().get(0));
            
            if(typeMatch(actual, expected)) {
                return expected;
            } else {
                throw new TypeComputerException("Type mismatch: The result should be boolean.", node);
            }
            
            
        } else if(type == ExpressionNodeTypes.POST_FIX_EXPR) {
            
        } else if(type == ExpressionNodeTypes.PREFIX_DECREMENT
               || type == ExpressionNodeTypes.PREFIX_INCREMENT) {
            // --int ++int
            
        } else if(type == ExpressionNodeTypes.PRIMARY_EXPR) {
            // if it has exactly 1 child and that child is a basic java primitive
            if(node.getChildren().size() == 1) {
                if(isPrimitive(node.getChildren().get(0))) {
                    return getType(node.getChildren().get(0));
                }
            }
            
            return callResolver(node, new Resolver());
            
        } else if(type == ExpressionNodeTypes.PRIMITIVE_TYPE) {
           return createWellKnownType(((IStringNode) node.getChildren().get(0)).getString());
            
        } else if(type == ExpressionNodeTypes.REFERENCE_TYPE) {
           return callResolver(node.getChildren().get(0), new Resolver());
            
        } else if(type == ExpressionNodeTypes.RELATIONAL_OP) {
            
        } else if(type == ExpressionNodeTypes.SHIFT) {
            
        } else if(type == ExpressionNodeTypes.SUPER_CALL) {
            
        } else if(type == ExpressionNodeTypes.TILDE) {
            
        } else if(type == ExpressionNodeTypes.TYPE_ARGUMENT) {
            
        } else {
            return super.computeType(node);
        }
        throw new TypeComputerException("Can not identify node type.", node);
    }
    
    private boolean arithmeticalBinding (ITypeBinding b1) {
       return ( b1.equals(FLOAT) || b1.equals(INTEGER) || b1.equals(CHAR) 
              || b1.equals(P_FLOAT) || b1.equals(P_INTEGER) || b1.equals(P_CHAR) );
       
    }
  
}
