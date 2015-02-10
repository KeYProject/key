package org.key_project.jmlediting.profile.jmlref.validator;

import org.eclipse.jdt.core.ICompilationUnit;
import org.key_project.jmlediting.core.dom.IASTNode;

public class JMLValidationContext implements IJMLValidationContext {

   private final IASTNode node;
   private final ICompilationUnit cu;

   /**
    * @param node
    * @param cu
    */
   public JMLValidationContext(final IASTNode node, final ICompilationUnit cu) {
      this.node = node;
      this.cu = cu;
   }

   @Override
   public IASTNode getJMLNode() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public ICompilationUnit getCompilationUnit() {
      // TODO Auto-generated method stub
      return null;
   }

}
