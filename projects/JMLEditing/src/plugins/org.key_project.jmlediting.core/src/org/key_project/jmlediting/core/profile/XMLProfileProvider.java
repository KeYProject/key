package org.key_project.jmlediting.core.profile;

import java.net.URI;

public class XMLProfileProvider implements IJMLProfileProvider {
   
   private final URI profileURI;
   
   public XMLProfileProvider(final URI profileURI) {
      if (profileURI == null) {
         throw new NullPointerException("Profile URI is null");
      }
      this.profileURI = profileURI;
   }

   @Override
   public IJMLProfile provideProfile() {
      // TODO Auto-generated method stub
      return null;
   }

}
