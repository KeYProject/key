package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.UnarySpecExpressionArgParser;

/**
 * The singleton keyword for KeY.
 *
 * @author Moritz Lichter
 *
 */
public class SingletonKeyword extends AbstractKeyword {

   /**
    * Creates a new singleton keyword instance.
    */
   public SingletonKeyword() {
      super("\\singleton");
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
      return new UnarySpecExpressionArgParser();
   }

}
