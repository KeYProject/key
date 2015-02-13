package org.key_project.jmlediting.core.validation;

import java.util.List;

import org.eclipse.jdt.core.dom.CompilationUnit;
import org.key_project.jmlediting.core.utilities.CommentRange;

public class JMLValidationContext implements IJMLValidationContext {

   private final String src;
   private final List<CommentRange> jmlComments;
   private final CompilationUnit javaAST;

   /**
    * @param node
    * @param cu
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
