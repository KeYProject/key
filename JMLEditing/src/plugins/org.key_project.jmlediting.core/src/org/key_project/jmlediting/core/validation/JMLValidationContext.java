package org.key_project.jmlediting.core.validation;

import java.util.List;
import java.util.Map;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.Comment;
import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.utilities.CommentRange;

/**
 * Implementation of IJMLValidationContext.
 *
 * @author David Giessing
 *
 */
public class JMLValidationContext implements IJMLValidationContext {

   /**
    * the Map from Leading Comments to ASTNodes.
    */
   private final Map<Comment, ASTNode> leadingCommentToNodeMap;

   /**
    * the Map from JML Comments to leading comments.
    */
   private final Map<CommentRange, Comment> jmlCommentToCommentMap;

   /**
    * the source to validate on.
    */
   private final String src;
   /**
    * the jmlComments in the Source.
    */
   private final List<CommentRange> jmlComments;
   /**
    * the Java AST contained in the source.
    */
   private final CompilationUnit javaAST;

   /**
    * The JML Parser used for this Validation.
    */
   private final IJMLParser jmlParser;

   /**
    * Creates a IJMLValidation context.
    *
    * @param assignedLeadingComments
    *           the Map from Leading Comments to ASTNodes
    *
    * @param assignedTrailingComments
    *           the Map from Trailing Comments to ASTNodes
    *
    * @param jmlCommentsToComments
    *           the Map from JML Comments to leading comments
    *
    *
    * @param src
    *           The Source
    *
    * @param jmlComments
    *           the List of JML Comments
    *
    * @param javaAST
    *           The Java AST
    *
    * @param jmlParser
    *           The jmlParser
    */
   public JMLValidationContext(
         final Map<Comment, ASTNode> assignedLeadingComments,
         final Map<CommentRange, Comment> jmlCommentsToComments,
         final String src, final List<CommentRange> jmlComments,
         final CompilationUnit javaAST, final IJMLParser jmlParser) {
      super();
      this.leadingCommentToNodeMap = assignedLeadingComments;
      this.jmlCommentToCommentMap = jmlCommentsToComments;
      this.src = src;
      this.jmlComments = jmlComments;
      this.javaAST = javaAST;
      this.jmlParser = jmlParser;
   }

   @Override
   public String getSrc() {
      return this.src;
   }

   @Override
   public List<CommentRange> getJMLComments() {
      return this.jmlComments;
   }

   @Override
   public CompilationUnit getJavaAST() {
      return this.javaAST;
   }

   @Override
   public IJMLParser getJMLParser() {
      return this.jmlParser;
   }

   @Override
   public ASTNode getNodeForLeadingComment(final Comment c) {
      return this.leadingCommentToNodeMap.get(c);
   }

   @Override
   public Comment getCommentForJMLComment(final CommentRange jmlComment) {
      return this.jmlCommentToCommentMap.get(jmlComment);
   }

}
