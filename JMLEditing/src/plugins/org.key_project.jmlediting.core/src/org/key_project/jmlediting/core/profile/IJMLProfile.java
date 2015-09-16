package org.key_project.jmlediting.core.profile;

import java.util.Set;

import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;
import org.key_project.jmlediting.core.resolver.IResolver;

/**
 * Defines a profile for a JML dialect. A profile consists of a unique id, a
 * name and a set of keywords, which are supported by the profile. A profile can
 * create a parse which parses JML comments belonging to the implemented JML
 * dialect.
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

   /**
    * Derives a new profile from this profile which can be edited. The created
    * profile does not contains any changes to this profile, but they may be
    * configured to the created profile later.
    *
    * @param id
    *           the id of the new profile
    * @param name
    *           the name of the profile
    * @return a new derived profile
    */
   IEditableDerivedProfile derive(String id, String name);

   /**
    * Returns a set of supported content descriptions which the user may use to
    * create other keywords dynamically.
    *
    * @return a set of all supported content descriptions, which is not
    *         modifiable
    */
   Set<IUserDefinedKeywordContentDescription> getSupportedContentDescriptions();

   /**
    * Returns a set of all {@link IKeywordSort}s defined in this profile.
    *
    * @return an immutable non null set
    */
   Set<IKeywordSort> getAvailableKeywordSorts();
   
   /**
    * Returns the resolver for this profile.
    * 
    * @return a resolver implementing {@link IResolver} to resolve nodes or
    *       null if no resolver was set by the profile.
    */
   IResolver getResolver();
}
