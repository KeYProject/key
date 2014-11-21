package org.key_project.jmlediting.core.profile.persistence;

import org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLParser;
import org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLWriter;

public class ProfileXMLFactory {
   
   private ProfileXMLFactory() {
   }
   
   public static IProfileXMLParser createParser() {
      return new ProfileXMLParser();
   }

   public static IProfileXMLWriter createWriter() {
      return new ProfileXMLWriter();
   }
   
}
