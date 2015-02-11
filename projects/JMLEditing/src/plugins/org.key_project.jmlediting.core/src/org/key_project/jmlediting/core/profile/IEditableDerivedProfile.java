package org.key_project.jmlediting.core.profile;

import org.key_project.jmlediting.core.profile.syntax.IKeyword;

/**
 * The {@link IEditableDerivedProfile} is a derived profile which content may be
 * edited on runtime.
 *
 * @author Moritz Lichter
 *
 */
public interface IEditableDerivedProfile extends IDerivedProfile {

   /**
    * Sets the name of the profile.
    *
    * @param newName
    *           the new name
    * @throws IllegalArgumentException
    *            if newName is null
    */
   void setName(String newName) throws IllegalArgumentException;

   /**
    * Enabled or disabled one of the keywords of the parent. By default all
    * parent keywords are enabled.
    *
    * @param parentKeyword
    *           the keyword of the parent to enabled or disable
    * @param disabled
    *           disable if true or enable if false
    * @throws IllegalArgumentException
    *            if the given keyword is not a member of the keywords of the
    *            parent
    */
   void setParentKeywordDisabled(IKeyword parentKeyword, boolean disabled)
         throws IllegalArgumentException;

   /**
    * Adds a new keyword which is additionally supported.
    *
    * @param newKeyword
    *           the new keyword, not allowed to be null
    * @throws IllegalArgumentException
    *            if newKeyword is null
    */
   void addKeyword(IKeyword newKeyword) throws IllegalArgumentException;

   /**
    * Removed the given keyword from the keywords, which are supported
    * additionally.
    *
    * @param oldKeyword
    *           the keyword to remove
    * @throws IllegalArgumentException
    *            if the keyword is null
    */
   void removeKeyword(IKeyword oldKeyword) throws IllegalArgumentException;

}
