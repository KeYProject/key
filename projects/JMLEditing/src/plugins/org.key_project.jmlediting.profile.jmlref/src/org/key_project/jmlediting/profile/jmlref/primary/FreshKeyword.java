package org.key_project.jmlediting.profile.jmlref.primary;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.SpecExpressionListArgParser;

/**
 * The implementation of the \fresh primary.
 *
 * @author Moritz Lichter
 *
 */
public class FreshKeyword extends AbstractKeyword {

   /**
    * Create a new keyword instance.
    */
   public FreshKeyword() {
      super("\\fresh");
   }

   @Override
   public IKeywordSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

   @Override
   public String getDescription() {
      return "The operator \fresh asserts that objects were freshly allocated; "
            + "for example, \fresh(x,y) asserts that x and y are not null and "
            + "that the objects bound to these identifiers were not allocated "
            + "in the pre-state.";
   }

   @Override
   public IKeywordParser createParser() {
      return new SpecExpressionListArgParser();
   }

}
