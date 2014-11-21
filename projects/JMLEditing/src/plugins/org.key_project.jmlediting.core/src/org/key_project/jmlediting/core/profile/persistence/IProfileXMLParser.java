package org.key_project.jmlediting.core.profile.persistence;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

public interface IProfileXMLParser {

   IJMLProfile parseProfile(URI uri) throws MalformedURLException, IOException, SAXException;
   IJMLProfile parseProfile(File file) throws IOException, SAXException;
   IJMLProfile parseProfile(InputSource source) throws IOException, SAXException;
   
}
