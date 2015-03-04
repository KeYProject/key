package org.key_project.jmlediting.core.profile.persistence.internal;

import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class LoadFromProfileKeywordPersistence extends KeywordPersistence {

   private final IJMLProfile parentProfile;

   public LoadFromProfileKeywordPersistence(final IDerivedProfile profile) {
      super(profile);
      this.parentProfile = profile.getParentProfile();
   }

   @Override
   protected void validateKeywordToPersist(final IKeyword keyword)
         throws ProfilePersistenceException {
      if (!this.parentProfile.getSupportedKeywords().contains(keyword)) {
         throw new ProfilePersistenceException(
               "The keyword is not contained by the parent profile");
      }
   }

   @Override
   protected IKeyword loadKeyword(final Class<? extends IKeyword> keywordClass)
         throws ProfilePersistenceException {
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
