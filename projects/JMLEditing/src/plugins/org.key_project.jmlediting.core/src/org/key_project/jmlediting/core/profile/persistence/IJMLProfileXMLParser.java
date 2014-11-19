package org.key_project.jmlediting.core.profile.persistence;

import java.io.File;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

public interface IJMLProfileXMLParser {

   IJMLProfile parseProfile(URI uri) throws MalformedURLException, IOException, SAXException, IllegalProfileXMLException;
   IJMLProfile parseProfile(File file) throws IOException, SAXException, IllegalProfileXMLException;
   IJMLProfile parseProfile(InputSource source) throws IOException, SAXException, IllegalProfileXMLException;
   
}
