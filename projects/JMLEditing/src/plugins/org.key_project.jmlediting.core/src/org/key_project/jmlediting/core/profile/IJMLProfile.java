package org.key_project.jmlediting.core.profile;

import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorSpecification;
import org.key_project.jmlediting.core.profile.syntax.IJMLGenericSpecification;

/**
 * Defines a profile for a JML variant.
 * 
 * @author Moritz Lichter
 *
 */
public interface IJMLProfile {

   /**
    * 
    * @return the name of the profile
    */
   String getName();

   /**
    * Returns a identifier for the profile which should be unique.
    * 
    * @return the identifier
    */
   String getIdentifier();

   /**
    * Returns a set of all supported behaviors of this profile. The returned set
    * is not allowed to be modified and is not null.
    * 
    * @return the set of supported behaviors
    */
   Set<IJMLBehaviorSpecification> getSupportedBehaviors();

   /**
    * Returns a set of all supported generics of this profile. The returned set
    * is not allowed to be modified and is not null.
    * 
    * @return the set of supported behaviors
    */
   Set<IJMLGenericSpecification> getSupportedGenerics();

   /**
    * Checks whether is profile is configurable. If it is, it returns an
    * {@link IConfigurableJMLProfile} which can be configured. It is not
    * necessary, that this is the same object, but it is required that changes
    * made to the returned {@link IConfigurableJMLProfile} also affect this
    * object. If the profile is not configurable, this methods returns null.
    * 
    * @return null if the profile is not configurable and otherwise an
    *         configurable profile
    */
   IConfigurableJMLProfile isConfigurable();

}
