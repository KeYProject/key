package org.key_project.jmlediting.core.profile.persistence;

import java.io.File;

import javax.xml.transform.stream.StreamResult;

import org.key_project.jmlediting.core.profile.IJMLProfile;

public abstract class AbstractProfileXMLWriter implements IProfileXMLWriter {

   @Override
   public void writeProfile(IJMLProfile profile, File file) {
      this.writeProfile(profile, new StreamResult(file));
   }

}
