package org.key_project.jmlediting.core.profile.persistence;

import java.io.File;

import javax.xml.transform.stream.StreamResult;

import org.key_project.jmlediting.core.profile.IJMLProfile;

public interface IProfileXMLWriter {
   
   void writeProfile(IJMLProfile profile, File file);
   void writeProfile(IJMLProfile profile, StreamResult result);

}
