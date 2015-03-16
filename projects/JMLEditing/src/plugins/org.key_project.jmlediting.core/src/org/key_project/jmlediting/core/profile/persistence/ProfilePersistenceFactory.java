package org.key_project.jmlediting.core.profile.persistence;

import org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence;

/**
 * Factory class for {@link IDerivedProfilePersistence}.
 * 
 * @author Moritz Lichter
 *
 */
public final class ProfilePersistenceFactory {

   /**
    * No instances.
    */
   private ProfilePersistenceFactory() {
   }

   /**
    * Returns a new {@link IDerivedProfilePersistence} which can be used to
    * persist profiles.
    *
    * @return a fresh persistence object
    */
   public static IDerivedProfilePersistence createDerivedProfilePersistence() {
      return new DerivedProfilePersistence();
   }

}
