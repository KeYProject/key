package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;

/**
 * A keyword content parser for {@link IJMLExpressionProfile} which uses a parse
 * function.
 *
 * @author Moritz Lichter
 *
 */
public abstract class JMLRefParseFunctionKeywordParser extends
      ParseFunctionKeywordParser<IJMLExpressionProfile> {

   /**
    * Creates a new parser.
    */
   public JMLRefParseFunctionKeywordParser() {
      super(IJMLExpressionProfile.class);
   }

   /**
    * Returns a parser which parses the same as the given one closed by a
    * semicolon.
    *
    * @param parser
    *           the parser to wrap
    * @return a new parser to parse the semicolon closed content of the given
    *         parser
    */
   public static JMLRefParseFunctionKeywordParser semicolonClosed(
         final JMLRefParseFunctionKeywordParser parser) {
      return new SemicolonClosedKeywordParser() {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLExpressionProfile profile) {
            return parser.createParseFunction(profile);
         }
      };
   }

}
