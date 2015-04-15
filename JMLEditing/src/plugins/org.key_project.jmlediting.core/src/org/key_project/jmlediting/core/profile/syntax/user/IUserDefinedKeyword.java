package org.key_project.jmlediting.core.profile.syntax.user;

import org.key_project.jmlediting.core.profile.syntax.IKeyword;

/**
 * The {@link IUserDefinedKeyword} implements a keyword which can defined by
 * users dynamically. The keyword is designed to be able to be persisted.
 *
 * @author Moritz Lichter
 *
 */
public interface IUserDefinedKeyword extends IKeyword {

   /**
    * Returns the description of the content. This encapsulated the parse
    * function and allows persisting the content.
    *
    * @return the description of the content of the keyword
    */
   IUserDefinedKeywordContentDescription getContentDescription();

   /**
    * Returns the closing character for the keyword, e.g. a semicolon. If no
    * character is allowed, this method returns null.
    * 
    * @return the closing character or null
    */
   Character getClosingCharacter();

}
