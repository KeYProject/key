package org.key_project.jmlediting.core.profile;

import java.net.URI;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.profile.persistence.impl.ProfileXMLParser;

/**
 * The {@link XMLProfileProvider} provides a jml profile from reading it from an
 * XML file. This class assumes that it is sufficient to read the profile once
 * from the xml.
 * 
 * @author Moritz Lichter
 *
 */
public class XMLProfileProvider implements IJMLProfileProvider {

   /**
    * The location of the profile.
    */
   private final URI uri;

   /**
    * Creates a new provider for an xml file located at the given URI.
    * 
    * @param uri
    *           the location of the profile, not allowed to be null
    */
   public XMLProfileProvider(final URI uri) {
      if (uri == null) {
         throw new NullPointerException("URI is not allowed to be null");
      }
      this.uri = uri;
   }

   @Override
   public IJMLProfile provideProfile() throws CoreException {
      // Parse the profile and return it
      ProfileXMLParser parser = new ProfileXMLParser();
      try {
         return parser.parseProfile(this.uri);
      }
      catch (Exception e) {
         throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID,
               "Failed to parse profile for URI " + uri, e));
      }
   }

   @Override
   public int hashCode() {
      final int prime = 31;
      int result = 1;
      result = prime * result + ((uri == null) ? 0 : uri.hashCode());
      return result;
   }

   @Override
   public boolean equals(Object obj) {
      if (this == obj)
         return true;
      if (obj == null)
         return false;
      if (getClass() != obj.getClass())
         return false;
      XMLProfileProvider other = (XMLProfileProvider) obj;
      if (uri == null) {
         if (other.uri != null)
            return false;
      }
      else if (!uri.equals(other.uri))
         return false;
      return true;
   }

}
