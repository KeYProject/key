package org.key_project.jmlediting.core.parser.internal;

import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class KeywordNode extends PrimitiveNode implements IKeywordNode {
   
   private final String keywordInstance;
   private final IKeyword keyword;

   public KeywordNode(int startOffset, int endOffset, IKeyword keyword, String keywordInstance) {
      super(startOffset, endOffset);
      this.keyword = keyword;
      this.keywordInstance = keywordInstance;
   }
   
   public String getKeywordInstance() {
      return keywordInstance;
   }

   @Override
   public int getType() {
      return NodeTypes.KEYWORD;
   }

   @Override
   public IKeyword getKeyword() {
      return keyword;
   }
   
   

}
