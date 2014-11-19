package de.key_project.jmlediting.profile.jmlref;

import java.net.URI;
import java.net.URISyntaxException;

import org.key_project.jmlediting.core.profile.URI_JMLProfileProvider;

public class JMLReferenceProfileProvider extends URI_JMLProfileProvider {
   
   public JMLReferenceProfileProvider() throws URISyntaxException {
      super(new URI("platform:/plugin/org.key_project.jmlediting.profile.jmlref/resources/jml_ref_profile.xml"));
   }

}
