package de.key_project.jmlediting.profile.jmlref;

import java.net.URI;
import java.net.URISyntaxException;

import org.key_project.jmlediting.core.profile.XMLProfileProvider;

public class JMLReferenceProfileProvider2 extends XMLProfileProvider {
   
   public JMLReferenceProfileProvider2() throws URISyntaxException {
      super(new URI("platform:/plugin/org.key_project.jmlediting.profile.jmlref/resources/jml_ref_profile2.xml"));
   }

}
