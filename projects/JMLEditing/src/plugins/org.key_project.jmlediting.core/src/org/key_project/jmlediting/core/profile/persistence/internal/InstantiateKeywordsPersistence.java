package org.key_project.jmlediting.core.profile.persistence.internal;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.osgi.framework.Bundle;
import org.osgi.framework.FrameworkUtil;

/**
 * An implementation of {@link KeywordPersistence} which creates a new instance
 * for coded keywords. Thus this persistence required the coded keywords to have
 * a nullary constructor. Otherwise they will neither be persisted nor read.
 * Only profiles of classes inside an OSGI bundle with a symbolic name are
 * persisted
 *
 * @author Moritz Lichter
 *
 */
public class InstantiateKeywordsPersistence extends KeywordPersistence {

   /**
    * Creates a new persistence for the given profile.
    *
    * @param profile
    *           the profile that contains the keywords to persist
    */
   public InstantiateKeywordsPersistence(final IJMLProfile profile) {
      super(profile);
   }

   @Override
   protected void validateCodedKeywordToPersist(final IKeyword keyword)
         throws ProfilePersistenceException {
      // Require each keyword to have a nullary constructor
      try {
         keyword.getClass().getConstructor();
      }
      catch (final NoSuchMethodException e) {
         throw new ProfilePersistenceException(
               "Cannot persist the keyword because it does not contains a "
                     + "nullary constructor and is not located in the parent profile",
               e);
      }

      // All keywords have to come from an OSGI bundle with a symbolic name
      final Bundle bundle = FrameworkUtil.getBundle(keyword.getClass());
      if (bundle == null || "".equals(bundle.getSymbolicName())) {
         throw new ProfilePersistenceException(
               "Class is not of a bundle with a bundle but this is "
                     + "requires to persist the keyword");
      }
   }

   @Override
   protected IKeyword loadCodedKeywordFromClass(
         final Class<? extends IKeyword> keywordClass)
         throws ProfilePersistenceException {
      try {
         // Create an object from the nullary constructor
         final Object newInstance = keywordClass.getConstructor().newInstance();
         return (IKeyword) newInstance;
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
