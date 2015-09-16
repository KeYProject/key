package org.key_project.jmlediting.profile.jmlref;

import java.util.Set;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;

public class DerivedExpressionProfile extends
      DerivedProfile<IJMLExpressionProfile> implements IJMLExpressionProfile {

    /**
     * The resolver of this profile.
     */
    private final Resolver resolver = new Resolver();

    public DerivedExpressionProfile(final String name, final String identifier,
         final IJMLExpressionProfile parentProfile) {
      super(name, identifier, parentProfile);
   }

   @Override
   public Set<IJMLPrimary> getSupportedPrimaries() {
      return this.getParentProfile().getSupportedPrimaries();
   }

   @Override
   public Set<ParseFunction> getPrimarySuffixExtensions() {
      return this.getParentProfile().getPrimarySuffixExtensions();
   }

   
   
   // TODO: added a private final resolver variable for the class, can be wrong
    @Override
    public IResolver getResolver() {
        // TODO Auto-generated method stub
        return this.resolver;
    }

   
}
