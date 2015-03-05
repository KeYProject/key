package de.uka.ilkd.key.symbolic_execution.profile;

import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.Profile;

/**
 * A {@link DefaultProfileResolver} which returns {@link SymbolicExecutionJavaProfile#getDefaultInstance()}.
 * @author Martin Hentschel
 */
public class SymbolicExecutionJavaProfileDefaultProfileResolver implements DefaultProfileResolver {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getProfileName() {
      return SymbolicExecutionJavaProfile.NAME;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Profile getDefaultProfile() {
      return SymbolicExecutionJavaProfile.getDefaultInstance();
   }
}
