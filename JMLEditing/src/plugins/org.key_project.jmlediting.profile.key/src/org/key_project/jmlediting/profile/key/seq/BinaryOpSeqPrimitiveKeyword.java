package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.BinarySpecExpressionArgParser;

/**
 * A seq primitive that works on two arguments.
 *
 * @author Moritz Lichter
 *
 */
public abstract class BinaryOpSeqPrimitiveKeyword extends AbstractKeyword {

   /**
    * Creates a new {@link BinaryOpSeqPrimitiveKeyword} with the given keyword.
    * 
    * @param keyword
    *           the first keyword
    * @param keywords
    *           other keywords
    */
   public BinaryOpSeqPrimitiveKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywordSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

   @Override
   public IKeywordParser createParser() {
      return new BinarySpecExpressionArgParser();
   }

}
