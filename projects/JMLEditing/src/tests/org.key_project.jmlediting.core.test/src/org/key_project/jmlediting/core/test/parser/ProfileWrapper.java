package org.key_project.jmlediting.core.test.parser;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfileAE;

public class ProfileWrapper {

   private static IJMLProfile getReferenceProfile() {
      try {
         return JMLProfileManagement.instance().getProfileFromIdentifier(
               new JMLReferenceProfileAE().getIdentifier());
      }
      catch (final NullPointerException e) {
         return new JMLReferenceProfileAE();
      }
   }

   public static IJMLProfile testProfile = getReferenceProfile();

}
