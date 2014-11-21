package org.key_project.jmlediting.core.profile;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;

/**
 * Implements a basic {@link JMLProfile}. It is not configurable but this is not
 * an invariant of this class. Subclasses may be able to be configured.
 * 
 * @author Moritz Lichter
 *
 */
public class JMLProfile implements IJMLProfile {

   /**
    * The name of the profile.
    */
   protected String name;
   /**
    * The identifier of the profile.
    */
   protected final String identifier;
   /**
    * The set of supported behaviors.
    */
   protected final Set<IJMLBehaviorSpecification> supportedBehaviors;
   /**
    * The set of supported generics.
    */
   protected final Set<IJMLGenericSpecification> supportedGenerics;

   /**
    * Creates a new {@link JMLProfile} with given name and identifier and
    * supported specifications. The specifications will be copied, so the sets
    * cannot be modified from outside.
    * 
    * @param name
    *           the name of the profile, not allowed to be null
    * @param identifier
    *           the unique identifier of this profile. not allowed to be null
    * @param supportedBehaviorSpecs
    *           the supported behavior specifications, not allowed to be null
    * @param supportedGenericSpecs
    *           the supported generic specifications
    */
   public JMLProfile(final String name, final String identifier,
         Set<IJMLBehaviorSpecification> supportedBehaviorSpecs,
         Set<IJMLGenericSpecification> supportedGenericSpecs) {
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
      this.supportedBehaviors = new HashSet<IJMLBehaviorSpecification>(
            supportedBehaviorSpecs);
      this.supportedGenerics = new HashSet<IJMLGenericSpecification>(
            supportedGenericSpecs);
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
   public Set<IJMLBehaviorSpecification> getSupportedBehaviors() {
      return Collections.unmodifiableSet(this.supportedBehaviors);
   }

   @Override
   public Set<IJMLGenericSpecification> getSupportedGenerics() {
      return Collections.unmodifiableSet(this.supportedGenerics);
   }

   @Override
   public IConfigurableJMLProfile isConfigurable() {
      return null;
   }

}
