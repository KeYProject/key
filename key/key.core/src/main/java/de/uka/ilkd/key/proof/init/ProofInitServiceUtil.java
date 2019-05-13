package de.uka.ilkd.key.proof.init;

import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.ServiceConfigurationError;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.reflection.ClassLoaderUtil;

/**
 * Provides static utility methods to get the following service:
 * <ul>
 *    <li>{@link POExtension} listed at {@code META-INF/services/de.uka.ilkd.key.proof.init.POExtension}</li>
 *    <li>{@link DefaultProfileResolver} listed at {@code META-INF/services/de.uka.ilkd.key.proof.init.DefaultProfileResolver}</li>
 * </ul>
 * @author Martin Hentschel
 */
public final class ProofInitServiceUtil {
   /**
    * The available {@link POExtension}s.
    */
   private static final ImmutableList<POExtension> poExtensions = createOperationPOExtension();
   
   /**
    * All available {@link DefaultProfileResolver}.
    */
   private static final Map<String, DefaultProfileResolver> resolver = createDefaultProfileResolver();
   
   /**
    * Forbid instances.
    */
   private ProofInitServiceUtil() {
   }
   
   /**
    * Returns the {@link POExtension} which supports the given {@link ProofOblInput}.
    * @param po The {@link ProofOblInput} for which {@link POExtension} are requested.
    * @return The available {@link POExtension}s.
    */
   public static ImmutableList<POExtension> getOperationPOExtension(ProofOblInput po) {
      ImmutableList<POExtension> result = ImmutableSLList.nil();
      for (POExtension extension : poExtensions) {
         if (extension.isPOSupported(po)) {
            result = result.prepend(extension);
         }
      }
      return result;
   }

   /**
    * Creates the {@link POExtension}s.
    * @return The available {@link POExtension}s.
    */
   private static ImmutableList<POExtension> createOperationPOExtension() {
      ImmutableList<POExtension> extensions = ImmutableSLList.nil();
      Iterator<POExtension> iter = ClassLoaderUtil.loadServices(POExtension.class).iterator();
      while (iter.hasNext()) {
         try {
            POExtension extension = iter.next();
            extensions = extensions.prepend(extension);
         }
         catch (ServiceConfigurationError e) {
            // Nothing to do, in case that a POExtension is not available. ProofObligation itself is fully functional.
         }
      }
      return extensions;
   }

   /**
    * <p>
    * Returns the {@link Profile} for the given name.
    * </p>
    * <p>
    * It is typically used in the {@link Thread} of the user interface.
    * Other instances of this class are typically only required to 
    * use them in different {@link Thread}s (not the UI {@link Thread}).
    * </p>
    * @param profileName The name of the requested {@link Profile}.
    * @return The {@link Profile} with the given name for usage in the {@link Thread} of the user interface or {@code null} if not available.
    */
   public static Profile getDefaultProfile(String profileName) {
      DefaultProfileResolver resolver = ProofInitServiceUtil.getDefaultProfileResolver(profileName);
      if (resolver != null) {
         return resolver.getDefaultProfile();
      }
      else {
         return null;
      }
   }
   
   /**
    * Returns the {@link DefaultProfileResolver} for the given profile name.
    * @param profileName The name of the profile.
    * @return The corresponding {@link DefaultProfileResolver} or {@code null} if not available.
    */
   public static DefaultProfileResolver getDefaultProfileResolver(String profileName) {
      return resolver.get(profileName);
   }
   
   /**
    * Creates all available {@link DefaultProfileResolver}.
    * @return All available {@link DefaultProfileResolver}.
    */
   private static Map<String, DefaultProfileResolver> createDefaultProfileResolver() {
      Map<String, DefaultProfileResolver> result = new HashMap<String, DefaultProfileResolver>();
      Iterator<DefaultProfileResolver> iter = ClassLoaderUtil.loadServices(DefaultProfileResolver.class).iterator();
      while (iter.hasNext()) {
         try {
            DefaultProfileResolver resolver = iter.next();
            result.put(resolver.getProfileName(), resolver);
         }
         catch (ServiceConfigurationError e) {
            // Nothing to do, in case that a DefaultProfileResolver is not available. In such a case the corresponding Profile will not be available as well.
         }
      }
      return result;
   }
}
