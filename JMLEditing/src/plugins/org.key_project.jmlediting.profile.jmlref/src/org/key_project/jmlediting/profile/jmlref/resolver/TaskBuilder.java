package org.key_project.jmlediting.profile.jmlref.resolver;

import java.util.LinkedList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;

/**
 * Class to build a list of {@link ResolverTask}s for a given {@link IASTNode} by calling
 * {@link #buildResolverTask(IASTNode)}.
 * 
 * @author Christopher Beckmann
 * 
 */
public class TaskBuilder {

   private final LinkedList<ResolverTask> tasks; // the task list which should be build and
                                                 // returned

   /**
    * Constructs a TaskBuilder and initializes the task list.
    */
   public TaskBuilder() {
      tasks = new LinkedList<ResolverTask>();
   }

   /**
    * Builds the {@link ResolverTask} list by stepping through the given {@link IASTNode} and
    * creating new resolver tasks or saving more information conditional on the type
    * information of the nodes.
    * 
    * @param jmlNode - the {@link IASTNode} that is supposed to be resolved.
    * @throws ResolverException is thrown, if the jmlNode isn't built correctly.
    */
   protected final LinkedList<ResolverTask> buildResolverTask(final IASTNode jmlNode)
            throws ResolverException {

      tasks.add(new ResolverTask());

      try {
         // This calls all the functions that build the resolver task list.
         // it's either a String (as in some assignable clauses or when the typeComputer
         // calls the resolver to resolve a type name) or it is a primary expression,
         // when called from a normal source that tries to resolve fields or methods.
         final boolean result = isReferenceType(jmlNode) 
                             || isString(jmlNode)
                             || isPrimaryExpr(jmlNode);
         if (result == false) {
            throw new ResolverException("Given IASTNode is not resolvable/ not supported.",
                     jmlNode, null);
         }

      }
      catch (final NullPointerException e) {
         throw new ResolverException("Given IASTNode is not resolvable. "
                  + "A NullPointerException occured while trying to access children.",
                  jmlNode, e);
      }

      return tasks;

   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link ExpressionNodeTypes}.{@code PRIMARY_EXPR}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isPrimaryExpr(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
         // PRIMARY
         final IASTNode firstChildren = node.getChildren().get(0);
         if (!isPrimaryExpr(node.getChildren().get(0))) {
            // Primaries may be cascaded.
            result = isIdentifier(firstChildren) || isJmlPrimary(firstChildren)
                     || isJavaKeyword(firstChildren) || isCast(firstChildren);
         }
         // Process the Children of the Node
         if (node.getChildren().size() > 1) {
            result = isList(node.getChildren().get(1));
         }
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link ExpressionNodeTypes}.{@code JAVA_KEYWORD}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isJavaKeyword(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.JAVA_KEYWORD) {
         tasks.getLast().setKeyword(true);
         result = isString(node.getChildren().get(0));
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link ExpressionNodeTypes}.{@code JML_PRIMARY}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isJmlPrimary(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.JML_PRIMARY) {
         // PRIMARY -> JML_PRIMARY
         result = isKeyword(node.getChildren().get(0));
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link NodeTypes}. {@code KEYWORD}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isKeyword(final IASTNode node) {
      boolean result = false;
      if (node.getType() == NodeTypes.KEYWORD
               && ((IKeywordNode) node).getKeywordInstance().equals("\\result")) {
         // PRIMARY -> JML_PRIMARY -> []
         tasks.getLast().setKeyword(true);
         tasks.getLast().setResolveString(((IKeywordNode) node).getKeywordInstance());

         result = true;
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link ExpressionNodeTypes}.{@code IDENTIFIER}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isIdentifier(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.IDENTIFIER) {
         // PRIMARY -> IDENTIFIER
         result = isString(node.getChildren().get(0));
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link NodeTypes}. {@code STRING}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isString(final IASTNode node) {
      boolean result = false;
      if (node.getType() == NodeTypes.STRING) {
         // PRIMARY -> IDENTIFIER -> STRING
         tasks.getLast().setResolveString(((IStringNode) node).getString());
         tasks.getLast().setNode((IStringNode) node);
         result = true;
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link NodeTypes}. {@code LIST}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isList(final IASTNode node) {
      boolean result = false;
      if (node.getType() == NodeTypes.LIST) {
         // PRIMARY -> IDENTIFIER -> STRING
         // -> LIST
         for (final IASTNode child : node.getChildren()) {
            result = isMethodCall(child) || isMemberAccess(child) || isArrayAccess(child) || isInvKeyword(child) || isSeq(child);
         }
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link ExpressionNodeTypes}.{@code ARRAY_ACCESS}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isArrayAccess(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.ARRAY_ACCESS) {
         // PRIMARY -> []
         // -> LIST -> ARRAY_ACCESS
         final IStringNode save = tasks.getLast().getNode();

         tasks.add(new ResolverTask());
         tasks.getLast().setArrayAcess(true);
         tasks.getLast().setNode(save);
         result = true;
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link ExpressionNodeTypes}.
    * {@code METHOD_CALL_PARAMETERS}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isMethodCall(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.METHOD_CALL_PARAMETERS) {
         // PRIMARY -> IDENTIFIER -> STRING
         // -> LIST -> METHOD_CALL
         tasks.getLast().setMethod(true);

         result = isExpressionList(node.getChildren().get(0))
                  || isEmptyList(node.getChildren().get(0));
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link NodeTypes}. {@code NONE}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isEmptyList(final IASTNode node) {
      // PRIMARY -> IDENTIFIER -> STRING
      // -> LIST -> METHOD_CALL -> NONE
      return node.getType() == NodeTypes.NONE;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link ExpressionNodeTypes}.{@code EXPRESSION_LIST}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isExpressionList(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.EXPRESSION_LIST) {
         // PRIMARY -> IDENTIFIER -> STRING
         // -> LIST -> METHOD_CALL -> EXPRESSION_LIST
         for (final IASTNode child : node.getChildren()) {
            tasks.getLast().getParameters().add(child);
            result = true;
         }
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link ExpressionNodeTypes}.{@code MEMBER_ACCESS}
    * 
    * @param node - the {@link IASTNode} to get information from
    * @return true, if the node and every child node is correct.
    */
   private final boolean isMemberAccess(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.MEMBER_ACCESS) {
         // PRIMARY -> IDENTIFIER -> STRING
         // -> LIST -> MEMBER_ACCESS
         tasks.add(new ResolverTask());
         tasks.getLast().setNode((IStringNode) node.getChildren().get(1));
         tasks.getLast().setResolveString(tasks.getLast().getNode().getString());
         result = true;
      }

      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It should be called on an
    * {@link IASTNode} that has the type {@link ExpressionNodeTypes}.{@code CAST}
    * 
    * @param node - the {@link IASTNode} to get information from.
    * @return true, if the node and every child node is correct.
    */
   private final boolean isCast(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.CAST) {
         if (node.getChildren().size() > 0) {
            result = isReferenceType(node.getChildren().get(0));
         }
      }
      return result;
   }

   /**
    * This method is part of the ResolverTask building process. It is needed when a cast
    * expression is needed to be resolved, i.e. to find out to which class some object is
    * casted to.
    * 
    * @param node - the {@link IASTNode} to get information from.
    * @return true, if the node and every child node is correct.
    */
   private final boolean isReferenceType(final IASTNode node) {
      boolean result = false;
      if (node.getType() == ExpressionNodeTypes.REFERENCE_TYPE) {
         result = true;
         // Such a node type is build like this
         // ReferenceType(Name(String, String, String,...))
         // More than one String is used when the cast goal is fully
         // qualified like (java.lang.String)
         final List<IASTNode> children = node.getChildren().get(0).getChildren();
         for (int i = 0; i < children.size(); i++) {
            tasks.getLast().setClass(true);
            isString(children.get(i));
            // add a new task for the next String if there is still one more
            // String
            if (i + 1 < children.size()) {
               tasks.add(new ResolverTask());
            }
         }
      }
      return result;
   }

   /**
    * This method checks if the given {@link IASTNode} is a Seq node.
    * This node is used for array accesses of the type array[*].
    * @param node node to check.
    * @return true if it is a Seq node and thus in fact an array access.
    */
   private boolean isSeq(final IASTNode node) {
      boolean result = false;
      if (node.getType() == NodeTypes.SEQ) {
         final IStringNode save = tasks.getLast().getNode();

         tasks.add(new ResolverTask());
         tasks.getLast().setArrayAcess(true);
         tasks.getLast().setNode(save);
         result = true;
      }
      return result;
   }

   /**
    * This method checks if the given {@link IASTNode} is an \inv keyword. 
    * Instead of being part of the MemberAccess node, it is saved as a Keyword node 
    * as a child in the list node.
    * @param node the node to check.
    * @return true if it is an \inv keyword. False else.
    */
   private boolean isInvKeyword(final IASTNode node) {
      boolean result = false;
      if (node.getType() == NodeTypes.KEYWORD && ((IKeywordNode) node).getKeywordInstance().equals("\\inv")) {
         result = true;
      }  
      return result;
   }

}
