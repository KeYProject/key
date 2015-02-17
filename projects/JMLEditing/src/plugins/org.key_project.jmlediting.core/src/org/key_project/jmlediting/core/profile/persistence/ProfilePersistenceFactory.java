package org.key_project.jmlediting.core.profile.persistence;

import org.key_project.jmlediting.core.profile.persistence.internal.DerivedProfilePersistence;

public class ProfilePersistenceFactory {

   public IDerivedProfilePersistence createDerivedProfilePersistence() {
      return new DerivedProfilePersistence();
   }

}
