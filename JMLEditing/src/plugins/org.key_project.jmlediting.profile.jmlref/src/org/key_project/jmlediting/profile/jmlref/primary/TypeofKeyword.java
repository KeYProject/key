package org.key_project.jmlediting.profile.jmlref.primary;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.UnarySpecExpressionArgParser;

/**
 * The implementation of the \typeof keyword.
 *
 * @author Moritz Lichter
 *
 */
public class TypeofKeyword extends AbstractKeyword {

   /**
    * Creates a new keyword instance.
    */
   public TypeofKeyword() {
      super("\\typeof");
   }

   @Override
   public IKeywordSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

   @Override
   public String getDescription() {
      return "The operator \\typeof returns the most-specific dynamic type of "
            + "an expression's value";
   }

   @Override
   public IKeywordParser createParser() {
      return new UnarySpecExpressionArgParser();
   }

}
