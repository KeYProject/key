package org.key_project.jmlediting.profile.key.test;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.profile.key.KeyProfile;

public class KeyProfileTestUtils {

   private static IJMLProfile keyProfile = new KeyProfile();

   public static IJMLProfile keyProfile() {
      return keyProfile;
   }

}
