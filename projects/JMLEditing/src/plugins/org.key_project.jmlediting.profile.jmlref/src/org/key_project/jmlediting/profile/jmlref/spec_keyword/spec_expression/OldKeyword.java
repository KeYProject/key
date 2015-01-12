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
      // TODO Auto-generated method stub
      return null;
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
