package org.key_project.jmlediting.core.validation;

import java.util.List;

import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.utilities.CommentRange;

/**
 * Implementation of IJMLValidationContext.
 *
 * @author David Giessing
 *
 */
public class JMLValidationContext implements IJMLValidationContext {

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
    * Creates a IJMLValidation context.
    *
    * @param src
    *           The Source
    *
    * @param jmlComments
    *           the List of JML Comments
    *
    * @param javaAST
    *           The Java AST
    */
   public JMLValidationContext(final String src,
         final List<CommentRange> jmlComments, final CompilationUnit javaAST) {
      this.src = src;
      this.jmlComments = jmlComments;
      this.javaAST = javaAST;
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

}
