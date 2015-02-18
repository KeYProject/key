package org.key_project.jmlediting.core.test.parser;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLProfileManagement;
import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfileAE;

public class ProfileWrapper {

   public static IJMLProfile testProfile = JMLProfileManagement
         .getProfileFromIdentifier(new JMLReferenceProfileAE().getIdentifier());

}
