package org.key_project.jmlediting.profile.jmlref.validator;

import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;

public class JMLValidationContext implements IJMLValidationContext {

   private final IASTNode node;
   private final ICompilationUnit cu;
   private final List<CommentRange> jmlComments;

   /**
    * @param node
    * @param cu
    */
   public JMLValidationContext(final IASTNode node, final ICompilationUnit cu,
         final List<CommentRange> jmlComments) {
      this.node = node;
      this.cu = cu;
      this.jmlComments = jmlComments;
   }

   @Override
   public IASTNode getJMLNode() {
      // TODO Auto-generated method stub
      return this.node;
   }

   @Override
   public ICompilationUnit getCompilationUnit() {
      // TODO Auto-generated method stub
      return this.cu;
   }

   @Override
   public List<CommentRange> getJMLComments() {
      // TODO Auto-generated method stub
      return this.jmlComments;
   }

}
