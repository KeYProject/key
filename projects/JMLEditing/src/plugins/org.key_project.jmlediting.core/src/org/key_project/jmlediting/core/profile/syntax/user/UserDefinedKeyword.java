package org.key_project.jmlediting.core.profile.syntax.user;

import java.util.Set;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordAutoProposer;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.ParseFunctionKeywordParser;

/**
 * An implementation of the {@link IUserDefinedKeyword}.
 *
 * @author Moritz Lichter
 *
 */
public class UserDefinedKeyword extends AbstractKeyword implements
      IUserDefinedKeyword {

   /**
    * The description of the content which encapsulated the parser.
    */
   private final IUserDefinedKeywordContentDescription contentDescription;
   /**
    * The description of the keyword.
    */
   private final String description;
   /**
    * The closing character.
    */
   private final char closingCharacter;

   /**
    * Creates a new {@link UserDefinedKeyword}.
    *
    * @param keywords
    *           the keywords, not allowed to be null
    * @param contentDescription
    *           the description of the content, not allowed to be null
    * @param description
    *           the description of the keyword, not allowed to be null
    * @param closingCharacter
    *           the closing character for this keyword, may be null
    */
   public UserDefinedKeyword(final Set<String> keywords,
         final IUserDefinedKeywordContentDescription contentDescription,
         final String description, final Character closingCharacter) {
      super(keywords);
      if (contentDescription == null) {
         throw new IllegalArgumentException(
               "Content description is not allowed to be null");
      }
      if (description == null) {
         throw new IllegalArgumentException(
               "Description is not allowed to be null");
      }
      this.contentDescription = contentDescription;
      this.description = description;
      this.closingCharacter = closingCharacter;
   }

   @Override
   public IUserDefinedKeywordContentDescription getContentDescription() {
      return this.contentDescription;
   }

   @Override
   public IKeywordParser createParser() {
      // Get the parse function from the content description.
      return new ParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(final IJMLProfile profile) {
            return UserDefinedKeyword.this.contentDescription
                  .getContentParseFunction(profile,
                        UserDefinedKeyword.this.closingCharacter);
         }
      };
   }

   @Override
   public IKeywordAutoProposer createAutoProposer() {
      return null;
   }

   @Override
   public String getDescription() {
      return this.description;
   }

   @Override
   public Character getClosingCharacter() {
      return this.closingCharacter;
   }

}
