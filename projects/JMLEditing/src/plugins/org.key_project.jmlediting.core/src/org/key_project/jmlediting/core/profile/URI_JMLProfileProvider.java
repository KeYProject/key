package org.key_project.jmlediting.core.profile;

import java.net.URI;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.profile.persistence.JMLProfileXMLParser;

public class URI_JMLProfileProvider implements IJMLProfileProvider {
   
   private final URI uri;
   
   public URI_JMLProfileProvider(final URI uri) {
      if (uri == null) {
         throw new NullPointerException("URI is not allowed to be null");
      }
      this.uri = uri;
   }

   @Override
   public IJMLProfile provideProfile() throws CoreException {
      JMLProfileXMLParser parser = new JMLProfileXMLParser();
      try {
         return parser.parseProfile(this.uri);
      }
      catch (Exception e) {
         throw new CoreException(new Status(IStatus.ERROR, Activator.PLUGIN_ID, "Failed to parse profile for URI " + uri, e));
      }
   }

}
