package org.key_project.jmlediting.core.profile.persistence.internal;

import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

/**
 * An implementation of {@link KeywordPersistence} which loads keywords from the
 * parent profile by searching for a profile with the same class! It does not
 * work if the parent contains multiple keywords with the same class
 *
 * @author Moritz Lichter
 *
 */
public class LoadFromProfileKeywordPersistence extends KeywordPersistence {

   /**
    * The parent profile.
    */
   private final IJMLProfile parentProfile;

   /**
    * Creates a new {@link LoadFromProfileKeywordPersistence} for the given
    * {@link IDerivedProfile}.
    *
    * @param profile
    *           the profile from which coded keywords should be loaded from the
    *           parent
    */
   public LoadFromProfileKeywordPersistence(final IDerivedProfile profile) {
      super(profile);
      this.parentProfile = profile.getParentProfile();
   }

   @Override
   protected void validateCodedKeywordToPersist(final IKeyword keyword)
         throws ProfilePersistenceException {
      // Keyword must be contained in the parent
      if (!this.parentProfile.getSupportedKeywords().contains(keyword)) {
         throw new ProfilePersistenceException(
               "The keyword is not contained by the parent profile");
      }
      // And the parent is only allowed to have one keyword of the class
      final Class<? extends IKeyword> keywordClass = keyword.getClass();
      int numKeywordWithClass = 0;
      for (final IKeyword parentKeyword : this.parentProfile
            .getSupportedKeywords()) {
         if (parentKeyword.getClass() == keywordClass) {
            numKeywordWithClass++;
            if (numKeywordWithClass > 1) {
               throw new ProfilePersistenceException(
                     "The parent profile contains multiple keywords of class "
                           + keywordClass.getName());
            }
         }
      }
   }

   @Override
   protected IKeyword loadCodedKeywordFromClass(
         final Class<? extends IKeyword> keywordClass)
         throws ProfilePersistenceException {
      // Search for a keyword with the given class in the parent profile
      for (final IKeyword keyword : this.parentProfile.getSupportedKeywords()) {
         if (keyword.getClass() == keywordClass) {
            return keyword;
         }
      }
      throw new ProfilePersistenceException(
            "No keyword with the given class \"" + keywordClass.getName()
                  + "\" final was found");
   }
}
