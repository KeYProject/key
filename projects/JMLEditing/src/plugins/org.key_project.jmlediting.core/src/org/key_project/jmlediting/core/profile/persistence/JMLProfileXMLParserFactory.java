package org.key_project.jmlediting.core.profile.persistence;

import org.key_project.jmlediting.core.profile.persistence.impl.JMLProfileXMLParser;

public class JMLProfileXMLParserFactory {
   
   private JMLProfileXMLParserFactory() {
   }
   
   public static IJMLProfileXMLParser createParser() {
      return new JMLProfileXMLParser();
   }

}
