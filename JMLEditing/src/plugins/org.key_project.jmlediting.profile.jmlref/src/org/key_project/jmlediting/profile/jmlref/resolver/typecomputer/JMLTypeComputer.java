package org.key_project.jmlediting.profile.jmlref.resolver.typecomputer;

import javax.xml.crypto.dsig.keyinfo.RetrievalMethod;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.internal.compiler.lookup.TypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.ITypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputerException;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;

/** Computes the types of given {@link IASTNodes}.
 * 
 * @author Christopher Beckmann
 *
 */
public class JMLTypeComputer extends TypeComputer implements ITypeComputer {

    public JMLTypeComputer(final ICompilationUnit compilationUnit) {
        super(compilationUnit, new Resolver());
    }
    
    public JMLTypeComputer(final ICompilationUnit compilationUnit, final IResolver resolver) {
       super(compilationUnit, resolver);
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
           // type_of(String[])
           
        } else if(type == ExpressionNodeTypes.ARRAY_DIM_DECL) {
         
        } else if(type == ExpressionNodeTypes.ARRAY_INITIALIZER) {
        
        } else if(type == ExpressionNodeTypes.ASSIGNMENT) {
           // set myGostVar := jmlExpression;
           //return Type of wanted element
           return computeType(node.getChildren().get(0));

        } else if(type == ExpressionNodeTypes.BINARY_AND 
               || type == ExpressionNodeTypes.BINARY_OR
               || type == ExpressionNodeTypes.BINARY_EXCLUSIVE_OR) {
            return createWellKnownType("boolean"); 
           
        } else if(type == ExpressionNodeTypes.CAST) {
           
           // If type is primitive Type .. TypeComputer has to handle it.
           return computeType(node.getChildren().get(0));
            
        } else if(type == ExpressionNodeTypes.CONDITIONAL_OP) {
           // condition ? exp1 : exp2;
        
        } else if(type == ExpressionNodeTypes.EQUALITY) {
            // the 2 sides must be of the same type
           return createWellKnownType("boolean");
        
        } else if(type == ExpressionNodeTypes.EQUIVALENCE_OP) {
           // <=>
           return createWellKnownType("boolean");
        
        } else if(type == ExpressionNodeTypes.EXPRESSION_LIST) {
        
        } else if(type == ExpressionNodeTypes.IDENTIFIER) {
            
        } else if(type == ExpressionNodeTypes.IMPLIES) {
           // ==> child should be primary
           return createWellKnownType("boolean");
              
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
            else {
                return createWellKnownType("boolean");
            }
            
        } else if(type == ExpressionNodeTypes.MULT
               || type == ExpressionNodeTypes.ADDITIVE) {
            if(node.getChildren().size() % 2 != 1 || node.getChildren().size() == 1) {
               return null;
            //TODO: Error erstellen throw new TypeComputerException("Arythmetic operation ecpects a sceond operand", node);
            }
            ITypeBinding operand;
            ITypeBinding savedType = P_CHAR;
            for(final IASTNode child : node.getChildren()) {
                if(child.getType() != NodeTypes.STRING) {
                    operand = computeType(child);
                    if (arithmeticalBinding(operand)) {
                       if(operand.isEqualTo(FLOAT) || operand.isEqualTo(P_FLOAT)) {
                          savedType = P_FLOAT;
                       } else if(operand.isEqualTo(INTEGER) || operand.isEqualTo(P_INTEGER)) {
                          if(!savedType.isEqualTo(P_FLOAT)) {
                             savedType = P_INTEGER;
                          }
                       }
                    } else {
                       return null; // TODO: Create Error
                    }
                }
            }
            return savedType;
            
            
        } else if (type == ExpressionNodeTypes.MINUS
               || type == ExpressionNodeTypes.PLUS) {
           //+int
           ITypeBinding operator = computeType(node.getChildren().get(1));
           if (operator.isEqualTo(createWellKnownType("double")) || operator.isEqualTo(createWellKnownType("java.lang.Double"))){
              return operator;
           }
           if (operator.isEqualTo(FLOAT) || operator.isEqualTo(P_FLOAT)){
              return P_FLOAT;
           }
           return P_INTEGER;
        
        } else if(type == ExpressionNodeTypes.NEW_EXPRESSION) {
           //new bla | first child is string node second is Reference Type
            return computeType(node.getChildren().get(1));
            
            
        } else if(type == ExpressionNodeTypes.NOT) {
            // !boolean
           return (createWellKnownType("boolean"));
           
        } else if(type == ExpressionNodeTypes.POST_FIX_EXPR) {
           //i++ increase ||| first element primary that gets increased second is string ++/--
           return computeType(node.getChildren().get(0));
            
        } else if(type == ExpressionNodeTypes.PREFIX_DECREMENT
               || type == ExpressionNodeTypes.PREFIX_INCREMENT) {
            // --int ++int
           return computeType(node.getChildren().get(1));
            
        } else if(type == ExpressionNodeTypes.PRIMARY_EXPR) {
            // if it has exactly 1 child and that child is a basic java primitive
            if(node.getChildren().size() == 1) {
                if(isPrimitive(node.getChildren().get(0))) {
                    return getType(node.getChildren().get(0));
                }
            }
            
            return callResolver(node);
            
        } else if(type == ExpressionNodeTypes.PRIMITIVE_TYPE) {
           return createWellKnownType(((IStringNode) node.getChildren().get(0)).getString());
            
        } else if(type == ExpressionNodeTypes.REFERENCE_TYPE) {
           return callResolver(node);
            
        } else if(type == ExpressionNodeTypes.RELATIONAL_OP) {
           return createWellKnownType("boolean");
            
        } else if(type == ExpressionNodeTypes.SHIFT) {
           return computeType(node.getChildren().get(0)); 
           
        } else if(type == ExpressionNodeTypes.SUPER_CALL) {
            
        } else if(type == ExpressionNodeTypes.TILDE) {
           return createWellKnownType("int");
            
        } else if(type == ExpressionNodeTypes.TYPE_ARGUMENT) {
           
        } else {
            return super.computeType(node);
        }
        throw new TypeComputerException("Can not identify node type.", node);
    }
    
    private boolean arithmeticalBinding (final ITypeBinding b1) {
       return b1.isEqualTo(FLOAT) || b1.isEqualTo(INTEGER) || b1.isEqualTo(CHAR) 
              || b1.isEqualTo(P_FLOAT) || b1.isEqualTo(P_INTEGER) || b1.isEqualTo(P_CHAR);
       
    }
  
}
