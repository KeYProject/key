package org.key_project.jmlediting.core.parser.internal;

import java.util.List;

import org.key_project.jmlediting.core.dom.IMethodSpecification;
import org.key_project.jmlediting.core.dom.ISpecificationCase;
import org.key_project.jmlediting.core.dom.NodeTypes;

public class MethodSpecification extends ASTNode implements
      IMethodSpecification {
   
   private boolean isExtendingSpecification;
   private List<ISpecificationCase> specCases;

   public MethodSpecification(int startOffset, int endOffset,
         boolean isExtendingSpecification, List<ISpecificationCase> specCases) {
      super(startOffset, endOffset);
      this.isExtendingSpecification = isExtendingSpecification;
      this.specCases = specCases;
   }

   @Override
   public boolean isExtendingSpecification() {
      return this.isExtendingSpecification;
   }

   @Override
   public List<ISpecificationCase> getSpecificationCases() {
      return this.specCases;
   }

   @Override
   public int getType() {
      return NodeTypes.METHOD_SPECIFICATION;
   }

}
