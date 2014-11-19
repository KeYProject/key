package org.key_project.jmlediting.core.profile;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;

/**
 * The {@link ConfigurableJMLProfile} allows changing the supported JML language
 * elements at runtime. So it can be modified by the user. The name and
 * identifier of the profile is fixed and cannot be changed.
 * 
 * @author Moritz Lichter
 *
 */
public class ConfigurableJMLProfile implements IJMLProfile {

   /**
    * The name of the profile.
    */
   private String name;
   /**
    * The identifier of the profile.
    */
   private final String identifier;
   /**
    * The set of supported behaviors.
    */
   private final Set<IJMLBehaviorSpecification> supportedBehaviors;
   /**
    * The set of supported generics.
    */
   private final Set<IJMLGenericSpecification> supportedGenerics;

   /**
    * Creates a new {@link ConfigurableJMLProfile} with given name and
    * identifier.The identifier will be fixed for the lifetime of this object.
    * 
    * @param name
    *           the name of the profile, not allowed to be null
    * @param identifier
    *           the unique identifier of this profile. not allowed to be null
    */
   public ConfigurableJMLProfile(final String name, final String identifier) {
      super();
      if (identifier == null) {
         throw new NullPointerException(
               "The identifier is not allowed to be null");
      }
      this.setName(name);
      this.identifier = identifier;
      this.supportedBehaviors = new HashSet<IJMLBehaviorSpecification>();
      this.supportedGenerics = new HashSet<IJMLGenericSpecification>();
   }

   @Override
   public String getName() {
      return this.name;
   }

   /**
    * Sets the name of the profile.
    * 
    * @param name
    *           the new name, not allowed to be null
    */
   public void setName(final String name) {
      if (name == null) {
         throw new NullPointerException("Cannot set Null name");
      }
      this.name = name;
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

   /**
    * Adds the given specification to the supported generic specifications of
    * this profile.
    * 
    * @param spec
    *           the new specification, not allowed to be null
    */
   public void addSupportGeneric(final IJMLGenericSpecification spec) {
      if (spec == null) {
         throw new NullPointerException("Cannot add a null specification");
      }
      this.supportedGenerics.add(spec);
   }

   /**
    * Removes the given specification from the supported generic specifications
    * of this profile.
    * 
    * @param spec
    *           the specification to remove
    * @return whether the specification was removed, false if it was not
    *         contained in this profile
    */
   public boolean removeSupportedGeneric(final IJMLGenericSpecification spec) {
      return this.supportedGenerics.remove(spec);
   }

   /**
    * Adds the given specification to the supported behavior specifications of
    * this profile.
    * 
    * @param spec
    *           the new specification, not allowed to be null
    */
   public void addSupportedBehavior(final IJMLBehaviorSpecification spec) {
      if (spec == null) {
         throw new NullPointerException("Cannot add a null specification");
      }
      this.supportedBehaviors.add(spec);
   }

   /**
    * Removes the given specification from the supported behavior specifications
    * of this profile.
    * 
    * @param spec
    *           the specification to remove
    * @return whether the specification was removed, false if it was not
    *         contained in this profile
    */
   public boolean removeSupportedBehavior(final IJMLBehaviorSpecification spec) {
      return this.supportedBehaviors.remove(spec);
   }

}
