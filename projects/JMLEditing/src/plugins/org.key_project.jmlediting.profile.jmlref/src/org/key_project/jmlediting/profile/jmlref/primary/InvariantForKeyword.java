package org.key_project.jmlediting.profile.jmlref.primary;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IJMLPrimaryKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.SpecExpressionParser;

/**
 * Implementation of the invariant keyword.
 *
 * @author Moritz Lichter
 *
 */
public class InvariantForKeyword extends AbstractKeyword implements
      IJMLPrimaryKeyword {

   /**
    * Creates new instance for the invariant_for keyword.
    */
   public InvariantForKeyword() {
      super("\\invariant_for");
   }

   @Override
   public String getDescription() {
      return "The \\invariant_for operator returns true just when its argument satisfies the "
            + "invariant of its static type.";
   }

   @Override
   public IKeywordParser createParser() {
      return new ParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(final IJMLProfile profile) {
            return ParserBuilder.brackets(new SpecExpressionParser(profile));
         }
      };
   }
}
