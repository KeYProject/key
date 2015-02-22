package org.key_project.jmlediting.core.profile.syntax.user;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;

/**
 * The {@link IUserDefinedKeywordContentDescription} encapsulates the parse
 * function for the keyword to allow persisting it. Instead of persisting the
 * parse function the unique ID of this class can be persisted.
 *
 * @author Moritz Lichter
 *
 */
public interface IUserDefinedKeywordContentDescription {

   /**
    * This enum specifies whether a content description allows a closing
    * character or not.
    * 
    * @author Moritz Lichter
    *
    */
   public static enum ClosingCharacterLaw {
      NOT_ALLOWED, ALLOWED, NECESSARY
   }

   /**
    * Returns a unique ID of the content descriptions.
    *
    * @return the unique id of this description
    */
   String getId();

   /**
    * Returns a description of the content which can be presented to the user.
    *
    * @return the description
    */
   String getDescription();

   /**
    * Creates the content parse function for the keyword for the given profile.
    *
    * @param profile
    *           the profile to create the parse function for
    * @param closingChar
    *           the closing character or null if none
    * @return the content parse function for the keyword
    */
   ParseFunction getContentParseFunction(IJMLProfile profile,
         Character closingChar);

   /**
    * Returns whether this content may have, needs to or forbids beeing closed
    * by a character, e.g. a semicolon.
    *
    * @return the policy for closing characters
    */
   ClosingCharacterLaw getClosingCharacterLaw();
}