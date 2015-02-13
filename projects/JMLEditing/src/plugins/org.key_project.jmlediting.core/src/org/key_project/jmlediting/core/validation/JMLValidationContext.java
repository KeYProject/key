package org.key_project.jmlediting.core.validation;

import java.util.List;

import org.key_project.jmlediting.core.utilities.CommentRange;

public class JMLValidationContext implements IJMLValidationContext {

   private final String src;
   private final List<CommentRange> jmlComments;

   /**
    * @param node
    * @param cu
    */
   public JMLValidationContext(final String src,
         final List<CommentRange> jmlComments) {
      this.src = src;
      this.jmlComments = jmlComments;
   }

   @Override
   public String getSrc() {
      // TODO Auto-generated method stub
      return this.src;
   }

   @Override
   public List<CommentRange> getJMLComments() {
      // TODO Auto-generated method stub
      return this.jmlComments;
   }

}
