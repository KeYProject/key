package org.key_project.jmlediting.core.profile;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;

public interface IConfigurableJMLProfile extends IJMLProfile {

   /**
    * Sets the name of the profile.
    * 
    * @param name
    *           the new name, not allowed to be null
    */
   void setName(final String name);
   
   /**
    * Adds the given specification to the supported generic specifications of
    * this profile.
    * 
    * @param spec
    *           the new specification, not allowed to be null
    */
   void addSupportGeneric(final IJMLGenericSpecification spec);

   /**
    * Removes the given specification from the supported generic specifications
    * of this profile.
    * 
    * @param spec
    *           the specification to remove
    * @return whether the specification was removed, false if it was not
    *         contained in this profile
    */
   boolean removeSupportedGeneric(final IJMLGenericSpecification spec);

   /**
    * Adds the given specification to the supported behavior specifications of
    * this profile.
    * 
    * @param spec
    *           the new specification, not allowed to be null
    */
   void addSupportedBehavior(final IJMLBehaviorSpecification spec);

   /**
    * Removes the given specification from the supported behavior specifications
    * of this profile.
    * 
    * @param spec
    *           the specification to remove
    * @return whether the specification was removed, false if it was not
    *         contained in this profile
    */
   boolean removeSupportedBehavior(final IJMLBehaviorSpecification spec);
   
}
