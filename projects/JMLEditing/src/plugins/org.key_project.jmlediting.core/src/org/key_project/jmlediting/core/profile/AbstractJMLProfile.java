package org.key_project.jmlediting.core.profile;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IKeyword;

/**
 * Implements a basic {@link AbstractJMLProfile}. It is not configurable but
 * this is not an invariant of this class. Subclasses may be able to be
 * configured.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractJMLProfile implements IJMLProfile {

   /**
    * The name of the profile.
    */
   private final String name;
   /**
    * The identifier of the profile.
    */
   private final String identifier;
   /**
    * The set of supported keywords.
    */
   private final Set<IKeyword> supportedKeywords;

   /**
    * Creates a new {@link AbstractJMLProfile} with given name and identifier
    * and supported specifications. The specifications will be copied, so the
    * sets cannot be modified from outside.
    *
    * @param name
    *           the name of the profile, not allowed to be null
    * @param identifier
    *           the unique identifier of this profile. not allowed to be null
    * @param supportedGenericSpecs
    *           the supported generic specifications
    */
   public AbstractJMLProfile(final String name, final String identifier,
         final Set<IKeyword> supportedGenericSpecs) {
      super();
      if (identifier == null) {
         throw new NullPointerException(
               "The identifier is not allowed to be null");
      }
      if (name == null) {
         throw new NullPointerException("Cannot use Null name");
      }
      this.name = name;
      this.identifier = identifier;
      this.supportedKeywords = new HashSet<IKeyword>(supportedGenericSpecs);
   }

   /**
    * Creates an {@link AbstractJMLProfile} without supported keywords. Mainly
    * useful for testing.
    *
    * @param name
    *           the name of the profile
    * @param identifier
    *           the identifier
    */
   public AbstractJMLProfile(final String name, final String identifier) {
      this(name, identifier, Collections.<IKeyword> emptySet());
   }

   @Override
   public String getName() {
      return this.name;
   }

   @Override
   public String getIdentifier() {
      return this.identifier;
   }

   @Override
   public Set<IKeyword> getSupportedKeywords() {
      return Collections.unmodifiableSet(this.supportedKeywords);
   }

}
