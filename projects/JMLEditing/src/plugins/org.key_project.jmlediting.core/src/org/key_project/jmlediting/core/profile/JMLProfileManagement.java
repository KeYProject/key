package org.key_project.jmlediting.core.profile;

import java.io.IOException;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import javax.xml.transform.OutputKeys;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerConfigurationException;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IConfigurationElement;
import org.eclipse.core.runtime.IExtension;
import org.eclipse.core.runtime.IExtensionPoint;
import org.eclipse.core.runtime.Platform;
import org.eclipse.core.runtime.preferences.IEclipsePreferences;
import org.eclipse.core.runtime.preferences.InstanceScope;
import org.key_project.jmlediting.core.Activator;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceException;
import org.key_project.jmlediting.core.profile.persistence.ProfilePersistenceFactory;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.osgi.service.prefs.BackingStoreException;
import org.osgi.service.prefs.Preferences;
import org.w3c.dom.Document;
import org.xml.sax.InputSource;
import org.xml.sax.SAXException;

/**
 * This class helps managing the available JML profiles.
 *
 * @author Moritz Lichter
 *
 */
public final class JMLProfileManagement {

   private static final String JML_DERIVED_PROFILES = "JMLDerivedProfiles";
   private static final JMLProfileManagement INSTANCE = new JMLProfileManagement();

   public static JMLProfileManagement instance() {
      return INSTANCE;
   }

   /**
    * Private constructor to prohibit creating objects of this class.
    */
   private JMLProfileManagement() {

   }

   /**
    * A map implementing a cache for the profile objects. The cache caches the
    * created object by identifier. The cache also ensures that only one profile
    * objects exists for an identifier.
    */
   private final Map<String, IJMLProfile> profileCache = new HashMap<String, IJMLProfile>();

   /**
    * Returns a set of all JML profiles which are available. The set may be
    * empty.
    *
    * @return a unmodifiable set of the current JML profiles
    */
   public Set<IJMLProfile> getAvailableProfiles() {
      try {
         // First load profiles from extension points
         this.loadExtensionProfiles();
         // Then load the derived ones, because they need access to them of the
         // extenion points
         this.loadDerivedProfiles();
      }
      catch (final InvalidProfileException e) {
         throw new RuntimeException(e);
      }
      // No all profiles are in the cache
      return Collections.unmodifiableSet(new HashSet<IJMLProfile>(
            this.profileCache.values()));
   }

   private void cacheProfile(final IJMLProfile profile)
         throws InvalidProfileException {
      this.validateProfile(profile);
      this.profileCache.put(profile.getIdentifier(), profile);
   }

   private void loadExtensionProfiles() throws InvalidProfileException {
      // Get the extension point
      final IExtensionPoint extensionPoint = Platform.getExtensionRegistry()
            .getExtensionPoint("org.key_project.jmlediting.core.profiles");

      // Now check all provided extension points
      for (final IExtension extension : extensionPoint.getExtensions()) {
         for (final IConfigurationElement elem : extension
               .getConfigurationElements()) {
            try {
               final Object profileO = elem.createExecutableExtension("class");
               if (profileO instanceof IJMLProfile) {
                  final IJMLProfile profile = (IJMLProfile) profileO;
                  if (!this.profileCache.containsKey(profile.getIdentifier())) {
                     this.cacheProfile(profile);
                  }
                  else {
                     // An object for this identifier has already been created
                     // reuse it from the cache and throw away the created one
                  }
               }

            }
            catch (final CoreException e) {
               // Invalid class of the extension object
               throw new InvalidProfileException(
                     "Got invalid extension object", e);
            }

         }
      }
   }

   private void loadDerivedProfiles() throws InvalidProfileException {
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      final Preferences p = preferences.node(JML_DERIVED_PROFILES);
      try {
         final String[] profileKeys = p.keys();
         for (final String profileKey : profileKeys) {
            if (!this.profileCache.containsKey(profileKey)) {

               final String xmlContent = p.get(profileKey, null);
               if (xmlContent == null) {
                  throw new InvalidProfileException("Profile with id "
                        + profileKey + " not found");
               }

               try {

                  final Document xmlDoc = DocumentBuilderFactory.newInstance()
                        .newDocumentBuilder()
                        .parse(new InputSource(new StringReader(xmlContent)));
                  final IDerivedProfile profile = ProfilePersistenceFactory
                        .createDerivedProfilePersistence().read(xmlDoc);

                  if (!profile.getIdentifier().equals(profileKey)) {
                     throw new InvalidProfileException(
                           "Profile has a wrong id. Expected " + profileKey
                                 + " but got " + profile.getIdentifier());
                  }
                  this.cacheProfile(profile);

               }
               catch (final ParserConfigurationException e) {
                  // Should not occur
                  throw new InvalidProfileException(e);
               }
               catch (final SAXException e) {
                  throw new InvalidProfileException(
                        "Unable to parse the persisted profile " + profileKey,
                        e);
               }
               catch (final IOException e) {
                  throw new InvalidProfileException(
                        "Unable to read the profile " + profileKey, e);
               }
               catch (final ProfilePersistenceException e) {
                  throw new InvalidProfileException(
                        "Could not read the profile for id " + profileKey, e);
               }
            }
         }
      }
      catch (final BackingStoreException e) {
         throw new InvalidProfileException(
               "Failed to access the eclipse preferences", e);
      }
   }

   public void writeDerivedProfiles() throws InvalidProfileException {
      final IEclipsePreferences preferences = InstanceScope.INSTANCE
            .getNode(Activator.PLUGIN_ID);
      final Preferences p = preferences.node(JML_DERIVED_PROFILES);

      for (final IJMLProfile profile : this.getAvailableProfiles()) {

         // TODO only write profiles which are not from extension points
         if (profile instanceof IDerivedProfile) {
            try {
               final Document document = ProfilePersistenceFactory
                     .createDerivedProfilePersistence().persist(
                           (IDerivedProfile) profile);
               final TransformerFactory tf = TransformerFactory.newInstance();
               final Transformer transformer = tf.newTransformer();
               transformer.setOutputProperty(OutputKeys.OMIT_XML_DECLARATION,
                     "yes");
               final StringWriter writer = new StringWriter();
               transformer.transform(new DOMSource(document), new StreamResult(
                     writer));
               p.put(profile.getIdentifier(), writer.toString());
            }
            catch (final ProfilePersistenceException e) {
               throw new InvalidProfileException(
                     "Unable to persist the given profile", e);
            }
            catch (final TransformerConfigurationException e) {
               // TODO Auto-generated catch block
               e.printStackTrace();
            }
            catch (final TransformerException e) {
               // TODO Auto-generated catch block
               e.printStackTrace();
            }
         }
      }
   }

   public void addDerivedProfile(final IDerivedProfile newProfile)
         throws InvalidProfileException {
      this.cacheProfile(newProfile);
   }

   /**
    * Does some validations on the given profile to catch exceptions early on
    * not on runtime later. If validation is not successful, this method throws
    * an exception.
    *
    * @param profile
    *           the profile to validate
    */
   private void validateProfile(final IJMLProfile profile)
         throws InvalidProfileException {
      // Do some validations on the profile:
      try {
         for (final IKeyword keywort : profile.getSupportedKeywords()) {
            if (keywort.getSort() != null) {
               AbstractKeywordSort.validateContentOfInstanceField(keywort
                     .getSort());
            }
         }
      }
      catch (final Exception e) {
         throw new InvalidProfileException("Failed to validate the profile "
               + profile.getName(), e);
      }
   }

   /**
    * Returns all available JML profiles sorted by their names.
    *
    * @return the sorted list of profiles
    */
   public List<IJMLProfile> getAvailableProfilesSortedByName() {
      final List<IJMLProfile> profiles = new ArrayList<IJMLProfile>(
            this.getAvailableProfiles());
      Collections.sort(profiles, new Comparator<IJMLProfile>() {

         @Override
         public int compare(final IJMLProfile o1, final IJMLProfile o2) {
            return o1.getName().compareTo(o2.getName());
         }
      });
      return profiles;
   }

   /**
    * Returns the IJMLProfile for the given identifier or null if no profile is
    * found for the identifier.
    *
    * @param identifier
    *           the identifer of the profile
    * @return the profile or null
    */
   public IJMLProfile getProfileFromIdentifier(final String identifier) {
      IJMLProfile profile = this.profileCache.get(identifier);
      if (profile == null) {
         // Maybe the user did not call getAvailableProfiles, so the cache is
         // not filled up
         // Try this
         this.getAvailableProfiles();
         profile = this.profileCache.get(identifier);
      }
      return profile;
   }

}
