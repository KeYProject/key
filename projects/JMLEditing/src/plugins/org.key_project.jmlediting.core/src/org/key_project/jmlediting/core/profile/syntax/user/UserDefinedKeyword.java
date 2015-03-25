package org.key_project.jmlediting.core.profile.syntax.user;

import java.util.Set;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordAutoProposer;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;

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
   private final Character closingCharacter;
   private final IKeywordSort sort;

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
         final IKeywordSort sort,
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
      if (sort == null) {
         throw new IllegalArgumentException(
               "The sort is not allowed to be null");
      }
      this.contentDescription = contentDescription;
      this.description = description;
      this.closingCharacter = closingCharacter;
      this.sort = sort;
   }

   @Override
   public IUserDefinedKeywordContentDescription getContentDescription() {
      return this.contentDescription;
   }

   @Override
   public IKeywordParser createParser() {
      // Get the parse function from the content description
      // and append the content description
      final IKeywordParser content = UserDefinedKeyword.this.contentDescription
            .createKeywordParser();
      if (UserDefinedKeyword.this.closingCharacter == null) {
         return content;
      }

      final ParseFunction closed = ParserBuilder.closedBy(NodeTypes.NODE,
            content, UserDefinedKeyword.this.closingCharacter);

      return new IKeywordParser() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            return closed.parse(text, start, end);
         }

         @Override
         public void setProfile(final IJMLProfile profile) {
            content.setProfile(profile);
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

   @Override
   public IKeywordSort getSort() {
      return this.sort;
   }

}
