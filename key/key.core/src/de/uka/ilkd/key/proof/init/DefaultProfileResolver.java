package de.uka.ilkd.key.proof.init;

/**
 * Instances of this class are used to get a default {@link Profile} instance.
 * <p>
 * Instances are created once via {@link ProofInitServiceUtil#getDefaultProfile(String)}
 * and reused all the time. This means that {@link DefaultProfileResolver} are singletons and should not have a state.
 * @author Martin Hentschel
 */
public interface DefaultProfileResolver {
   /**
    * Returns the profile name.
    * @return The profile name.
    */
   public String getProfileName();
   
   /**
    * Returns the default {@link Profile} instance.
    * @return The default {@link Profile} instance.
    */
   public Profile getDefaultProfile();
}
