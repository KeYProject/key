package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.util.JavaBasicsParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.primary.AbstractJMLPrimaryKeyword;

/**
 * The implementation of the {@link OldKeyword}.
 *
 * @author Moritz Lichter
 *
 */
public class OldKeyword extends AbstractJMLPrimaryKeyword {

   /**
    * Creates a new instance of the old keyword.
    */
   public OldKeyword() {
      super("\\old");
   }

   @Override
   public String getDescription() {
      return "An expression of the form \\old(Expr) refers to the value that the expression "
            + "Expr had in the pre-state of a method."
            + "\nAn expression of the form \\old(Expr, Label) refers to the value that the "
            + "expression Expr had when control last reached the statement label Label.";
   }

   @Override
   public IKeywordParser createParser() {
      return new JMLRefParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(
               final IJMLExpressionProfile profile) {
            /**
             * old-expression ::= \old ( spec-expression [ , ident ] )<br>
             * | \pre ( spec-expression )
             */
            return brackets(seq(new SpecExpressionParser(profile),
                  opt(separateBy(',', JavaBasicsParser.ident()))));
         }
      };
   }
}
