package org.key_project.jmlediting.core.profile.syntax;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;

/**
 * Implements an {@link IKeywordParser} which is profile specified. This class
 * caches the parser created for a profile until the parser is used for another
 * profile.
 *
 * @author Moritz Lichter
 *
 */
public abstract class ParseFunctionKeywordParser implements IKeywordParser {

   /**
    * The parser used to parse.
    */
   private ParseFunction mainParser;

   /**
    * Creates the profile specific parse function.
    * 
    * @param profile
    *           the profile for which to parse
    * @return the parse function to use for the given profile
    */
   protected abstract ParseFunction createParseFunction(IJMLProfile profile);

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      if (this.mainParser == null) {
         throw new IllegalStateException(
               "Cannot parse before a profile has been set");
      }
      return this.mainParser.parse(text, start, end);
   }

   @Override
   public void setProfile(final IJMLProfile profile) {
      this.mainParser = this.createParseFunction(profile);
      if (this.mainParser == null) {
         throw new NullPointerException(
               "createParseFunction returned a null parser");
      }
   }

}
