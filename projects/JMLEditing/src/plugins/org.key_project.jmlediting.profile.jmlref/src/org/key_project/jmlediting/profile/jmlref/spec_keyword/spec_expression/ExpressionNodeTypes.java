package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import org.key_project.jmlediting.core.dom.NodeTypes;

/**
 * This class contains final constants for types of nodes in the expression AST.
 *
 * @author Moritz Lichter
 *
 */
public final class ExpressionNodeTypes {

   /**
    * no instances.
    */
   private ExpressionNodeTypes() {

   }

   public static final int JAVA_KEYWORD = NodeTypes.getNewType("JavaKeyword");
   public static final int IDENTIFIER = NodeTypes.getNewType("Identifier");
   public static final int REFERENCE_TYPE = NodeTypes
         .getNewType("ReferenceType");
   public static final int PRIMITIVE_TYPE = NodeTypes
         .getNewType("PrimitiveType");
   public static final int NEW_EXPRESSION = NodeTypes
         .getNewType("NewExpression");
   public static final int TYPE_ARGUMENT = NodeTypes.getNewType("TypeArgument");
   public static final int EXPRESSION_LIST = NodeTypes
         .getNewType("ExpressionList");
   public static final int LOGICAL_OR = NodeTypes.getNewType("LogicalOr");
   public static final int LOGICAL_AND = NodeTypes.getNewType("LogicalAnd");
   public static final int BINARY_OR = NodeTypes.getNewType("BinaryOr");
   public static final int BINARY_AND = NodeTypes.getNewType("BinaryAnd");
   public static final int BINARY_EXCLUSIVE_OR = NodeTypes
         .getNewType("BinaryExclusiveOr");
   public static final int EQUALITY = NodeTypes.getNewType("Equality");
   public static final int ADDITIVE = NodeTypes.getNewType("Additive");
   public static final int SHIFT = NodeTypes.getNewType("Shift");
   public static final int MULT = NodeTypes.getNewType("Mult");
   public static final int ASSIGNMENT = NodeTypes.getNewType("Assignment");
   public static final int ARRAY_DIM_DECL = NodeTypes
         .getNewType("ArrayDimDecl");
   public static final int ARRAY_INITIALIZER = NodeTypes
         .getNewType("ArrayInitializer");
   public static final int JML_PRIMARY = NodeTypes.getNewType("JMLPrimary");
   public static final int MEMBER_ACCESS = NodeTypes.getNewType("MemberAccess");
   public static final int SUPER_CALL = NodeTypes
         .getNewType("SuperConstructorCall");
   public static final int ARRAY_ACCESS = NodeTypes.getNewType("ArrayAccess");
   public static final int METHOD_CALL_PARAMETERS = NodeTypes
         .getNewType("MethodCall");
   public static final int ARRAY_CLASS = NodeTypes.getNewType("ArrayClass");
   public static final int POST_FIX_EXPR = NodeTypes.getNewType("PostFixExpr");
   public static final int TILDE = NodeTypes.getNewType("Tilde");
   public static final int NOT = NodeTypes.getNewType("Not");
   public static final int CAST = NodeTypes.getNewType("Cast");
   public static final int PREFIX_INCREMENT = NodeTypes
         .getNewType("PrefixIncr");
   public static final int PREFIX_DECREMENT = NodeTypes
         .getNewType("PrefixDecr");
   public static final int PLUS = NodeTypes.getNewType("Plus");
   public static final int MINUS = NodeTypes.getNewType("Minus");
   public static final int RELATIONAL_OP = NodeTypes.getNewType("RelationalOp");
   public static final int EQUIVALENCE_OP = NodeTypes
         .getNewType("EquivalenceOp");
   public static final int CONDITIONAL_OP = NodeTypes
         .getNewType("ConditionalOp");
   public static final int IMPLIES = NodeTypes.getNewType("Implies");
   public static final int PRIMARY_EXPR = NodeTypes.getNewType("Primary");

}
