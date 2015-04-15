package org.key_project.jmlediting.profile.jmlref.test.utilities;

import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfileAE;

public class ProfileWrapper {

   private static IJMLExpressionProfile getReferenceProfile() {
      return new JMLReferenceProfileAE();
   }

   public static IJMLExpressionProfile testProfile = getReferenceProfile();

}
