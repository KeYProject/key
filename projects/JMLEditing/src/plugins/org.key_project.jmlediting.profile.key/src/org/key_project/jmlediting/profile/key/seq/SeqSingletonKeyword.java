package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.UnarySpecExpressionArgParser;

/**
 * The seq singleton keyword for KeY.
 *
 * @author Moritz Lichter
 *
 */
public class SeqSingletonKeyword extends AbstractKeyword {

   /**
    * Creates a new seq singleton keyword instance.
    */
   public SeqSingletonKeyword() {
      super("\\seq_singleton");
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
   public IKeywordSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

}
