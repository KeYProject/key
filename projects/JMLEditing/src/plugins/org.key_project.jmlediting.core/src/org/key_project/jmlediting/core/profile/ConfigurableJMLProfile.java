package org.key_project.jmlediting.core.profile;

import java.util.HashSet;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;

/**
 * The {@link ConfigurableJMLProfile} allows changing the supported JML language
 * elements at runtime. So it can be modified by the user. The identifier of the
 * profile is fixed and cannot be changed.
 * 
 * @author Moritz Lichter
 *
 */
public class ConfigurableJMLProfile extends JMLProfile implements
      IConfigurableJMLProfile {

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
      super(name, identifier, new HashSet<IJMLBehaviorSpecification>(),
            new HashSet<IJMLGenericSpecification>());
   }

   @Override
   public void setName(final String name) {
      if (name == null) {
         throw new NullPointerException("Cannot set Null name");
      }
      this.name = name;
   }

   @Override
   public void addSupportGeneric(final IJMLGenericSpecification spec) {
      if (spec == null) {
         throw new NullPointerException("Cannot add a null specification");
      }
      this.supportedGenerics.add(spec);
   }

   @Override
   public boolean removeSupportedGeneric(final IJMLGenericSpecification spec) {
      return this.supportedGenerics.remove(spec);
   }

   @Override
   public void addSupportedBehavior(final IJMLBehaviorSpecification spec) {
      if (spec == null) {
         throw new NullPointerException("Cannot add a null specification");
      }
      this.supportedBehaviors.add(spec);
   }

   @Override
   public boolean removeSupportedBehavior(final IJMLBehaviorSpecification spec) {
      return this.supportedBehaviors.remove(spec);
   }

   @Override
   public IConfigurableJMLProfile isConfigurable() {
      return this;
   }

}
