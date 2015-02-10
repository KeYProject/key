package org.key_project.jmlediting.profile.key.seq;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;

public class SeqConcatKeyword extends AbstractKeyword implements SeqPrimitiveKeyword {

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
             * \seq_concat ( seq-expr , seq-expr ) | ...
             */
            final SeqExpressionParser seqExpr = new SeqExpressionParser(profile);
            return brackets(seq(seqExpr, constant(","), seqExpr));
         }
      };
   }

}
