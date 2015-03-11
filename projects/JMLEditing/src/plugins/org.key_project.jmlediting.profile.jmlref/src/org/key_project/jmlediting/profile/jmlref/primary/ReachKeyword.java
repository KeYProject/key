package org.key_project.jmlediting.profile.jmlref.primary;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.profile.jmlref.parser.BracketSpecExpressionParser;

/**
 * Implementation of the \reach primary.
 *
 * @author Moritz Lichter
 *
 */
public class ReachKeyword extends AbstractKeyword {

   /**
    * Create a new keyword instance.
    */
   public ReachKeyword() {
      super("\\reach");
   }

   @Override
   public IKeywortSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

   @Override
   public String getDescription() {
      return "The \\reach expression allows one to refer to the set "
            + "of objects reachable from some particular object.";
   }

   @Override
   public IKeywordParser createParser() {
      return new BracketSpecExpressionParser();
   }

}
