package org.key_project.jmlediting.core.parser.internal;

import org.key_project.jmlediting.core.dom.ISpecificationStatement;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

public class SpecificationStatement extends ASTNode implements ISpecificationStatement{

   private ISpecificationStatementKeyword keyword;
   
   private String content;

   public SpecificationStatement(int startOffset, int endOffset,
         ISpecificationStatementKeyword keyword, String content) {
      super(startOffset, endOffset);
      this.keyword = keyword;
      this.content = content;
   }
   
   @Override
   public ISpecificationStatementKeyword getKeyword() {
      return this.keyword;
   }
   
   @Override
   public String getContent() {
      return this.content;
   }

   @Override
   public int getType() {
      return NodeTypes.SPECIFICATION_STATEMENT;
   }
   
}
