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

   private final Map<Comment, ASTNode> inverse;
   private final Map<Comment, ASTNode> inverseTrailing;
   private final Map<CommentRange, Comment> jmlCommentToInverse;
   private final Map<CommentRange, Comment> jmlCommentToInverseTrailing;
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
    * @param inverse
    *           the Map from Leading Comments to ASTNodes
    *
    * @param inverseTrailing
    *           the Map from Trailing Comments to ASTNodes
    *
    * @param jmlCommentToInverse
    *           the Map from JML Comments to leading comments
    *
    * @param jmlCommentToInverseTrailing
    *           the Map from JML Comments to trailing comments
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
   public JMLValidationContext(final Map<Comment, ASTNode> inverse,
         final Map<Comment, ASTNode> inverseTrailing,
         final Map<CommentRange, Comment> jmlCommentToInverse,
         final Map<CommentRange, Comment> jmlCommentToInverseTrailing,
         final String src, final List<CommentRange> jmlComments,
         final CompilationUnit javaAST, final IJMLParser jmlParser) {
      super();
      this.inverse = inverse;
      this.inverseTrailing = inverseTrailing;
      this.jmlCommentToInverse = jmlCommentToInverse;
      this.jmlCommentToInverseTrailing = jmlCommentToInverseTrailing;
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
      // TODO Auto-generated method stub
      return this.jmlParser;
   }

   @Override
   public Map<Comment, ASTNode> getInverse() {
      return this.inverse;
   }

   @Override
   public Map<Comment, ASTNode> getInverseTrailing() {
      return this.inverseTrailing;
   }

   @Override
   public Map<CommentRange, Comment> getJmlCommentToInverse() {
      return this.jmlCommentToInverse;
   }

   @Override
   public Map<CommentRange, Comment> getJmlCommentToInverseTrailing() {
      return this.jmlCommentToInverseTrailing;
   }
}
