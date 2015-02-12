package org.key_project.jmlediting.core.compilation;

import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.utilities.CommentRange;

public class JMLValidationContext implements IJMLValidationContext {

   private final IASTNode node;
   private final String src;
   private final List<CommentRange> jmlComments;

   /**
    * @param node
    * @param cu
    */
   public JMLValidationContext(final IASTNode node, final String src,
         final List<CommentRange> jmlComments) {
      this.node = node;
      this.src = src;
      this.jmlComments = jmlComments;
   }

   @Override
   public IASTNode getJMLNode() {
      // TODO Auto-generated method stub
      return this.node;
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
