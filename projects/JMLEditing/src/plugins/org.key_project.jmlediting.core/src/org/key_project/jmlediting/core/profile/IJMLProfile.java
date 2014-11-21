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

}
