package org.key_project.jmlediting.profile.jmlref.spec_keyword.requires;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AbstractGenericSpecificationKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.ParseFunctionGenericKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.PredicateParser;

/**
 * The requires keyword.
 *
 * @author Moritz Lichter
 *
 */
public class RequiresKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Creates a new instance for the requires keyword.
    */
   public RequiresKeyword() {
      super("requires");
   }

   @Override
   public String getDescription() {
      return "A requires clause specifies a precondition of method or constructor.";
   }

   @Override
   public IKeywordParser createParser() {
      return new ParseFunctionGenericKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLProfile profile) {
            /**
             * requires-clause ::= requires-keyword pred-or-not ; <br>
             * | requires-keyword \same ; <br>
             * requires-keyword ::= requires | pre <br>
             * | requires_redundantly | pre_redundantly <br>
             * pred-or-not ::= predicate | \not_specified
             */
            return alt(
                  new PredicateParser(profile),
                  keywords(JMLProfileHelper.filterKeywords(profile,
                        IRequiresValueKeyword.class), profile));
         }
      };
   }

}
