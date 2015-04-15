package org.key_project.jmlediting.core.profile.syntax.user;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

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
    * @return the content parse function for the keyword
    */
   IKeywordParser createKeywordParser();

}