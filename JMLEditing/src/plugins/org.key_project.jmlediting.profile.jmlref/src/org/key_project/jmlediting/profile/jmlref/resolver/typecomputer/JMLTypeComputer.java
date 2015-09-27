package org.key_project.jmlediting.profile.jmlref.resolver.typecomputer;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.typecomputer.ITypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputer;
import org.key_project.jmlediting.core.resolver.typecomputer.TypeComputerException;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;

/**
 * Computes the types of given {@link IASTNodes}.
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
      
      // We don't need a lot of those cases, because this class is only working for the Resolver.

      final int type = node.getType();

      if(type == ExpressionNodeTypes.ARRAY_ACCESS) {
         return null;

      } else if(type == ExpressionNodeTypes.ARRAY_CLASS) {
         // TODO: not implemented.
         return null;

      } else if(type == ExpressionNodeTypes.ARRAY_DIM_DECL) {
         // TODO: not implemented.
         return null;

      } else if(type == ExpressionNodeTypes.ARRAY_INITIALIZER) {
         // TODO: not implemented.
         return null;

      } else if(type == ExpressionNodeTypes.ASSIGNMENT) {
         // return Type of wanted element
         return computeType(node.getChildren().get(0));

      } else if(type == ExpressionNodeTypes.CAST) {
         // If type is primitive Type .. TypeComputer has to handle it.
         return computeType(node.getChildren().get(0));

      } else if(type == ExpressionNodeTypes.CONDITIONAL_OP) {
         // TODO: condition ? exp1 : exp2;
         return null;

      } else if(type == ExpressionNodeTypes.EXPRESSION_LIST) {
         return null;

      } else if(type == ExpressionNodeTypes.IDENTIFIER) {
         // return null here so we can go back and call the resolver with the primary node.
         return null;

      } else if(type == ExpressionNodeTypes.JAVA_KEYWORD) {
         // return null here so we can go back and call the resolver with the primary node.
         return null;
         // super / this / ?

      } else if(type == ExpressionNodeTypes.JML_PRIMARY) {
         // TODO check for specific keywords like \old and return the type of its child.
         // else return null because \result needs to be sent to the resolver.
         return null;
         // \result \old(...) ?

      } else if(type == ExpressionNodeTypes.LOGICAL_AND 
            || type == ExpressionNodeTypes.LOGICAL_OR 
            || type == ExpressionNodeTypes.NOT
            || type == ExpressionNodeTypes.IMPLIES 
            || type == ExpressionNodeTypes.EQUIVALENCE_OP 
            || type == ExpressionNodeTypes.EQUALITY
            || type == ExpressionNodeTypes.BINARY_AND 
            || type == ExpressionNodeTypes.BINARY_OR 
            || type == ExpressionNodeTypes.BINARY_EXCLUSIVE_OR
            || type == ExpressionNodeTypes.RELATIONAL_OP) {
         // & / | / ^ /
         // !
         // ==> child should be primary
         // <==>
         return createWellKnownType("boolean");

      } else if(type == ExpressionNodeTypes.MULT || type == ExpressionNodeTypes.ADDITIVE) {
         ITypeBinding operand;
         ITypeBinding savedType = P_CHAR;
         for(final IASTNode child : node.getChildren()) {
            if(child.getType() != NodeTypes.STRING) {
               operand = computeType(child);
               if(arithmeticalBinding(operand)) {
                  if(operand.isEqualTo(FLOAT) || operand.isEqualTo(P_FLOAT)) {
                     savedType = P_FLOAT;
                  } else if(operand.isEqualTo(INTEGER) || operand.isEqualTo(P_INTEGER)) {
                     if(!savedType.isEqualTo(P_FLOAT)) {
                        savedType = P_INTEGER;
                     }
                  }
               }
            }
         }
         return savedType;

      } else if(type == ExpressionNodeTypes.MINUS || type == ExpressionNodeTypes.PLUS) {
         // +int
         final ITypeBinding operator = computeType(node.getChildren().get(1));
         if(operator.isEqualTo(createWellKnownType("double")) || operator.isEqualTo(createWellKnownType("java.lang.Double"))) {
            return operator;
         }
         if(operator.isEqualTo(FLOAT) || operator.isEqualTo(P_FLOAT)) {
            return P_FLOAT;
         }
         return P_INTEGER;

      } else if(type == ExpressionNodeTypes.NEW_EXPRESSION 
            || type == ExpressionNodeTypes.PREFIX_DECREMENT
            || type == ExpressionNodeTypes.PREFIX_INCREMENT) {
         // --int ++int
         // new Object() | first child is string node second is Reference Type
         return computeType(node.getChildren().get(1));

      } else if(type == ExpressionNodeTypes.POST_FIX_EXPR) {
         // i++ increase ||| first element primary that gets increased second is
         // string ++/--
         return computeType(node.getChildren().get(0));

      } else if(type == ExpressionNodeTypes.PRIMARY_EXPR) {
         // if it has exactly 1 child and that child is a basic java primitive
         if(node.getChildren().size() == 1) {
            if(isPrimitive(node.getChildren().get(0))) {
               return getType(node.getChildren().get(0));
            }
            
            ITypeBinding result = null;

            result = computeType(node.getChildren().get(0));
            if(result != null) {
               return result;
            }
         }
         return callResolver(node);

      } else if(type == ExpressionNodeTypes.PRIMITIVE_TYPE) {
         return createWellKnownType(((IStringNode) node.getChildren().get(0)).getString());

      } else if(type == ExpressionNodeTypes.REFERENCE_TYPE) {
         return callResolver(node);

      } else if(type == ExpressionNodeTypes.SHIFT) {
         return computeType(node.getChildren().get(0));

      } else if(type == ExpressionNodeTypes.SUPER_CALL) {
         return null;

      } else if(type == ExpressionNodeTypes.TILDE) {
         return createWellKnownType("int");

      } else if(type == ExpressionNodeTypes.TYPE_ARGUMENT) {
         return null;

      } else {
         return super.computeType(node);
      }
   }

   private boolean arithmeticalBinding(final ITypeBinding b1) {
      return b1.isEqualTo(FLOAT) || b1.isEqualTo(INTEGER) || b1.isEqualTo(CHAR) || b1.isEqualTo(P_FLOAT) || b1.isEqualTo(P_INTEGER)
            || b1.isEqualTo(P_CHAR);

   }
}
