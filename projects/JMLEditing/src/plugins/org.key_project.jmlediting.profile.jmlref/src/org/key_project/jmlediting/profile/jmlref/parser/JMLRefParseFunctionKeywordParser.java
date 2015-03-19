package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;

public abstract class JMLRefParseFunctionKeywordParser extends
      ParseFunctionKeywordParser<IJMLExpressionProfile> {

   public JMLRefParseFunctionKeywordParser() {
      super(IJMLExpressionProfile.class);
   }

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
