package org.key_project.jmlediting.core.profile.persistence;

import org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence;

public final class ProfilePersistenceFactory {

   /**
    * No instances.
    */
   private ProfilePersistenceFactory() {
   }

   public static IDerivedProfilePersistence createDerivedProfilePersistence() {
      return new DerivedProfilePersistence();
   }

}
