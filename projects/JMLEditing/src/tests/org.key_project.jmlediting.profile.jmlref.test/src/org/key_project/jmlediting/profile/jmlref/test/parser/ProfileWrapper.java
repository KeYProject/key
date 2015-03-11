package org.key_project.jmlediting.profile.jmlref.test.parser;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfileAE;

public class ProfileWrapper {

   private static IJMLProfile getReferenceProfile() {
      return new JMLReferenceProfileAE();
   }

   public static IJMLProfile testProfile = getReferenceProfile();

}
