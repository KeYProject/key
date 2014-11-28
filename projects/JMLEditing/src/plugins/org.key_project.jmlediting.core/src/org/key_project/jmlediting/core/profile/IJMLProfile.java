package org.key_project.jmlediting.core.profile;

import java.util.Set;

import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

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
    * Returns a set of all supported keywords of this profile. The returned set
    * is not allowed to be modified and is not null.
    * 
    * @return the set of supported behaviors
    */
   Set<IKeyword> getSupportedKeywords();

   /**
    * Creates a new parser to parse JML for this profile. A parser created with
    * this method must only be used once. This allows the parser to cover some
    * state. But implementations of this method may return the same object
    * everytime if state is no problem.
    * 
    * @return a new parser to parse JML according to this profile
    */
   IJMLParser createParser();

}
