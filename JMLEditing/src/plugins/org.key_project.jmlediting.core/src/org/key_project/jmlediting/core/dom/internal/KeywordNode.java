package org.key_project.jmlediting.core.dom.internal;

import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

/**
 * Creates a new {@link KeywordNode} for a keyword found in the text.
 *
 * @author Moritz Lichter
 *
 */
public class KeywordNode extends PrimitiveNode implements IKeywordNode {

   /**
    * The actual keyword found.
    */
   private final String keywordInstance;
   /**
    * The {@link IKeyword} this node belongs to.
    */
   private final IKeyword keyword;

   /**
    * Creates a new Keyword node with the given keyword.
    *
    * @param startOffset
    *           the start offset
    * @param endOffset
    *           the end offset
    * @param keyword
    *           the {@link IKeyword} this node belongs to
    * @param keywordInstance
    *           the actual keyword found
    */
   public KeywordNode(final int startOffset, final int endOffset,
         final IKeyword keyword, final String keywordInstance) {
      super(startOffset, endOffset);
      this.keyword = keyword;
      this.keywordInstance = keywordInstance;
   }

   @Override
   public String getKeywordInstance() {
      return this.keywordInstance;
   }

   @Override
   public int getType() {
      return NodeTypes.KEYWORD;
   }

   @Override
   public IKeyword getKeyword() {
      return this.keyword;
   }

   @Override
   public String toString() {
      return "Keyword[" + this.getStartOffset() + "-" + this.getEndOffset()
            + "](" + this.keywordInstance + ")";
   }

   @Override
   public String prettyPrintAST() {
      return "Keyword(" + this.keywordInstance + ")";
   }

}
