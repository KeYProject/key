package org.key_project.jmlediting.core.profile.persistence;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.net.MalformedURLException;
import java.net.URI;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

/**
 * An abstract implementation for the {@link IJMLProfileXMLParser} which
 * redirects all parse methods to a single one which is left open for other
 * classes to implement.
 * 
 * @author Moritz Lichter
 *
 */
public abstract class AbstractJMLProfileXMLParser implements
      IJMLProfileXMLParser {

   @Override
   public IJMLProfile parseProfile(final URI uri) throws MalformedURLException,
         IOException, SAXException {
      return this.parseProfile(new InputSource(uri.toURL().openStream()));
   }

   @Override
   public IJMLProfile parseProfile(final File file) throws IOException, SAXException {
      return this.parseProfile(new InputSource(new FileInputStream(file)));
   }

}
