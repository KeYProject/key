package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.TrinarySpecExpressionArgParser;

/**
 * The seq put keyword for KeY.
 *
 * @author Moritz Lichter
 *
 */
public class SeqPutKeyword extends AbstractKeyword {

   /**
    * Creates a new seq put keyword instance.
    */
   public SeqPutKeyword() {
      super("\\seq_put");
   }

   @Override
   public IKeywordSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return new TrinarySpecExpressionArgParser();
   }

}
