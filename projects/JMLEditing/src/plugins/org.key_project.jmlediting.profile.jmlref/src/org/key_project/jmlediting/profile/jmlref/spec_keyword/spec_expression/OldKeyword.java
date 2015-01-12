package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.parseutil.JavaBasicsParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.ParseFunctionKeywordParser;

public class OldKeyword extends AbstractKeyword implements IJMLPrimaryKeyword {

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
      return new ParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(final IJMLProfile profile) {
            return brackets(seq(new SpecExpressionParser(profile),
                  opt(separateBy(',', JavaBasicsParser.ident()))));
         }
      };
   }
}
