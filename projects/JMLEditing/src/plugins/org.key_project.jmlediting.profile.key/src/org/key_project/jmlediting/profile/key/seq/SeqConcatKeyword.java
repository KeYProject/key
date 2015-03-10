package org.key_project.jmlediting.profile.key.seq;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class SeqConcatKeyword extends AbstractKeyword {

   public SeqConcatKeyword() {
      super("\\seq_concat");
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
            /**
             * seq-expr ::= ...| <br>
             * \seq_concat ( expr , expr ) | ...
             */
            final ExpressionParser expr = new ExpressionParser(profile);
            return brackets(seq(expr, constant(","), expr));
         }
      };
   }

   @Override
   public IKeywortSort getSort() {
      return SeqPrimitiveKeywordSort.INSTANCE;
   }

}
