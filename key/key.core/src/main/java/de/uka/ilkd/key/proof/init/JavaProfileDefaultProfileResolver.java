package de.uka.ilkd.key.proof.init;

/**
 * A {@link DefaultProfileResolver} which returns {@link JavaProfile#getDefaultProfile()}.
 * @author Martin Hentschel
 */
public class JavaProfileDefaultProfileResolver implements DefaultProfileResolver {
   /**
    * {@inheritDoc}
    */
   @Override
   public String getProfileName() {
      return JavaProfile.NAME;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Profile getDefaultProfile() {
      return JavaProfile.getDefaultInstance();
   }
}
