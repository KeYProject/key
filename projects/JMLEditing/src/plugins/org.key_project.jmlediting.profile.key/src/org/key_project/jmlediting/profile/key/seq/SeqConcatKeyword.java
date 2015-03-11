package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.parser.BinarySpecExpressionParser;

public class SeqConcatKeyword extends AbstractKeyword {

   public SeqConcatKeyword() {
      super("\\seq_concat");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return new BinarySpecExpressionParser();
   }

   @Override
   public IKeywortSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

}
