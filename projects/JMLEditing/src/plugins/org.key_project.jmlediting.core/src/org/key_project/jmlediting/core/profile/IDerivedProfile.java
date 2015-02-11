package org.key_project.jmlediting.core.profile;

import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IKeyword;

/**
 * The {@link IDerivedProfile} is a jml profile which has been derived from
 * another one. It may disable keywords of the parent profile and is able to add
 * new ones.
 *
 * @author Moritz Lichter
 *
 */
public interface IDerivedProfile extends IJMLProfile {

   /**
    * Returns the parent profile of the derived profile.
    *
    * @return the parent profile
    */
   IJMLProfile getParentProfile();

   /**
    * Checks whether the given keyword of the parent has been disabled by the
    * derived profile.
    *
    * @param keyword
    *           the keyword to check for
    * @return whether the keyword is disabled
    * @throws IllegalArgumentException
    *            when keyword is not a member of the keywords of the parent
    *            profile
    */
   boolean isParentKeywordDisabled(IKeyword keyword)
         throws IllegalArgumentException;

   /**
    * Returns a set of all additional keywords this profile provides. The set
    * can not be modified.
    *
    * @return all keywords supported additionally to the keywords of the parent
    */
   Set<IKeyword> getAdditionalKeywords();

}
