package org.key_project.jmlediting.core.profile.persistence.internal;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.osgi.framework.FrameworkUtil;

public class LoadFromProfileKeywordPersistence extends KeywordPersistence {

   private final IJMLProfile parentProfile;

   public LoadFromProfileKeywordPersistence(final IJMLProfile parentProfile) {
      super();
      this.parentProfile = parentProfile;
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
   protected IKeyword loadKeyword(final String keywordClassName,
         final String bundleId) throws ProfilePersistenceException {
      final boolean hasBundle = !"".equals(bundleId);
      for (final IKeyword keyword : this.parentProfile.getSupportedKeywords()) {
         if (keyword.getClass().getName().equals(keywordClassName)) {
            if (!hasBundle
                  || FrameworkUtil.getBundle(keyword.getClass())
                        .getSymbolicName().equals(bundleId)) {
               return keyword;
            }
         }
      }

      throw new ProfilePersistenceException(
            "No keyword with the given class \"" + keywordClassName + "\""
                  + (hasBundle ? "and bundle \"" + bundleId + "\"" : "")
                  + " was found");
   }

}
