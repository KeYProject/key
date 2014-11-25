package org.key_project.jmlediting.core.parser.internal;

import java.util.List;

import org.key_project.jmlediting.core.dom.ILightweightSpecification;
import org.key_project.jmlediting.core.dom.ISpecificationStatement;
import org.key_project.jmlediting.core.dom.NodeTypes;

public class LightweightSpecification extends ASTNode implements
      ILightweightSpecification {
   
   private List<ISpecificationStatement> statements;

   public LightweightSpecification(int startOffset, int endOffset, List<ISpecificationStatement> statements) {
      super(startOffset, endOffset);
      this.statements = statements;
   }

   @Override
   public List<ISpecificationStatement> getSpecificationStatements() {
      return statements;
   }

   @Override
   public int getType() {
      return NodeTypes.LIGHTWEIGHT_SPECIFICATION;
   }


}
