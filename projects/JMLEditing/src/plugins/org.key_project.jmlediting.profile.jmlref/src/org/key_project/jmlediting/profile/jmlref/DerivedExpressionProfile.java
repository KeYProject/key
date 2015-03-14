package org.key_project.jmlediting.profile.jmlref;

import java.util.Set;

import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.DerivedProfile;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;

public class DerivedExpressionProfile extends
      DerivedProfile<IJMLExpressionProfile> implements IJMLExpressionProfile {

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

}
