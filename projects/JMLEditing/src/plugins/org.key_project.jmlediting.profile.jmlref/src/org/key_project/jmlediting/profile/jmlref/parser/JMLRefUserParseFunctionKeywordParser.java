package org.key_project.jmlediting.profile.jmlref.parser;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;

/**
 * Defines a parse function keyword content parser which can be used to define
 * user keywords.
 *
 * @author Moritz Lichter
 *
 */
public abstract class JMLRefUserParseFunctionKeywordParser extends
      JMLRefParseFunctionKeywordParser implements
      IUserDefinedKeywordContentDescription {

   @Override
   public String getId() {
      return this.getClass().getName();
   }

   @Override
   public IKeywordParser createKeywordParser() {
      return new JMLRefParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(
               final IJMLExpressionProfile profile) {
            return JMLRefUserParseFunctionKeywordParser.this
                  .createParseFunction(profile);
         }
      };
   }

}
