package org.key_project.jmlediting.core.profile.persistence.internal;

import org.eclipse.core.runtime.Platform;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

public class InstantiateKeywordsPersistence extends KeywordPersistence {

   public InstantiateKeywordsPersistence(final IJMLProfile profile) {
      super(profile);
   }

   @Override
   protected void validateKeywordToPersist(final IKeyword keyword)
         throws ProfilePersistenceException {
      try {
         keyword.getClass().getConstructor();
      }
      catch (final NoSuchMethodException e) {
         throw new ProfilePersistenceException(
               "Cannot persist the keyword because it does not contains a "
                     + "nullary constructor and is not located in the parent profile",
               e);
      }

      final Bundle bundle = FrameworkUtil.getBundle(keyword.getClass());
      if (bundle == null || "".equals(bundle.getSymbolicName())) {
         throw new ProfilePersistenceException(
               "Class is not of a bundle with a bundle but this is requires to persist the keyword");
      }
   }

   @Override
   protected IKeyword loadKeyword(final String keywordClassName,
         final String bundleId) throws ProfilePersistenceException {
      final boolean hasBundle = !"".equals(bundleId);
      // Need to instantiate the class
      try {

         final Class<?> keywordClass;
         if (hasBundle) {
            keywordClass = Platform.getBundle(bundleId).loadClass(
                  keywordClassName);
         }
         else {
            throw new ProfilePersistenceException(
                  "Cannot instatiate a keyworword without a bundle");
         }

         final Object newInstance = keywordClass.getConstructor().newInstance();
         if (!(newInstance instanceof IKeyword)) {
            throw new ProfilePersistenceException(
                  "Class of keyword does not implement IKeyword");
         }
         return (IKeyword) newInstance;
      }
      catch (final ClassNotFoundException e) {
         throw new ProfilePersistenceException(
               "Failed to load keyword class \"" + keywordClassName
                     + "\" from bundle \"" + bundleId + "\"", e);
      }
      catch (final NoSuchMethodException e) {
         throw new ProfilePersistenceException(
               "Keyword class does not contains a nullary constructor", e);
      }
      catch (final Exception e) {
         throw new ProfilePersistenceException(
               "Failed to instantiate a new keyword instance", e);
      }
   }

}
