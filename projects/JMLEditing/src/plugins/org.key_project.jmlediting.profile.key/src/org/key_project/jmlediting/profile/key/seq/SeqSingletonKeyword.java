package org.key_project.jmlediting.profile.key.seq;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class SeqSingletonKeyword extends AbstractKeyword implements SeqPrimitiveKeyword {

   public SeqSingletonKeyword() {
      super("\\seq_singleton");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return new ParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(final IJMLProfile profile) {
            return ParserBuilder.brackets(new ExpressionParser(profile));
         }
      };
   }

}
