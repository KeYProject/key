package org.key_project.jmlediting.profile.jmlref.primary;

import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.TypeArgParser;

/**
 * The implementation of the \type primary.
 *
 * @author Moritz Lichter
 *
 */
public class TypeKeyword extends AbstractKeyword {

   /**
    * Returns a new type keyword.
    */
   public TypeKeyword() {
      super("\\type");
   }

   @Override
   public IKeywordSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

   @Override
   public String getDescription() {
      return "The operator \\type can be used to introduce literals of type "
            + "\\TYPE in expressions. An expression of the form \type(T), "
            + "where T is a type name, has the type \\TYPE. ";
   }

   @Override
   public IKeywordParser createParser() {
      return new TypeArgParser();
   }

}
