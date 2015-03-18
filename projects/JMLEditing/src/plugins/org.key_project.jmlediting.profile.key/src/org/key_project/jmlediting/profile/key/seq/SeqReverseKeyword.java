package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.parser.UnarySpecExpressionArgParser;

public class SeqReverseKeyword extends AbstractKeyword {

   public SeqReverseKeyword() {
      super("\\seq_reverse");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return new UnarySpecExpressionArgParser();
   }

   @Override
   public IKeywortSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

}
