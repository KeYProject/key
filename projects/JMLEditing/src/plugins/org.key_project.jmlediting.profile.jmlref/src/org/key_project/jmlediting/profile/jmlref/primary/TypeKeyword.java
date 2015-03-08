package org.key_project.jmlediting.profile.jmlref.primary;

import static org.key_project.jmlediting.core.parser.ParserBuilder.brackets;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.core.profile.syntax.JMLPrimaryKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

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
   public IKeywortSort getSort() {
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
      return new ParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(final IJMLProfile profile) {
            final SpecExpressionParser parser = new SpecExpressionParser(
                  profile);
            return brackets(parser.typeSpec());
         }
      };
   }

}
