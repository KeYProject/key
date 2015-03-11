package org.key_project.jmlediting.profile.key.test;

import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfile;
import org.key_project.jmlediting.profile.key.KeyProfile;

public class KeyProfileTestUtils {

   private static JMLReferenceProfile keyProfile = new KeyProfile();

   public static JMLReferenceProfile keyProfile() {
      return keyProfile;
   }

}
