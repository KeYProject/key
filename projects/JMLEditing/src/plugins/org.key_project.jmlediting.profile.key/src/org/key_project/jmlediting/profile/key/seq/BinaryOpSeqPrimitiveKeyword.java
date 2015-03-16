package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.parser.BinarySpecExpressionParser;

public abstract class BinaryOpSeqPrimitiveKeyword extends AbstractKeyword {

   public BinaryOpSeqPrimitiveKeyword(final String keyword,
         final String... keywords) {
      super(keyword, keywords);
   }

   @Override
   public IKeywortSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

   @Override
   public IKeywordParser createParser() {
      return new BinarySpecExpressionParser();
   }

}
