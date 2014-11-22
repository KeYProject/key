package org.key_project.jmlediting.core.profile;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

/**
 * Implements a basic {@link AbstractJMLProfile}. It is not configurable but this is not
 * an invariant of this class. Subclasses may be able to be configured.
 * 
 * @author Moritz Lichter
 *
 */
public abstract class AbstractJMLProfile implements IJMLProfile {

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
   protected final Set<IJMLBehaviorKeyword> supportedBehaviors;
   /**
    * The set of supported generics.
    */
   protected final Set<ISpecificationStatementKeyword> supportedGenerics;

   /**
    * Creates a new {@link AbstractJMLProfile} with given name and identifier and
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
   public AbstractJMLProfile(final String name, final String identifier,
         Set<IJMLBehaviorKeyword> supportedBehaviorSpecs,
         Set<ISpecificationStatementKeyword> supportedGenericSpecs) {
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
      this.supportedBehaviors = new HashSet<IJMLBehaviorKeyword>(
            supportedBehaviorSpecs);
      this.supportedGenerics = new HashSet<ISpecificationStatementKeyword>(
            supportedGenericSpecs);
   }
   
   public AbstractJMLProfile(final String name, final String identifier) {
      this(name, identifier, Collections.<IJMLBehaviorKeyword>emptySet(),Collections.<ISpecificationStatementKeyword>emptySet());
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
   public Set<IJMLBehaviorKeyword> getSupportedBehaviors() {
      return Collections.unmodifiableSet(this.supportedBehaviors);
   }

   @Override
   public Set<ISpecificationStatementKeyword> getSupportedSpecificationStatementKeywords() {
      return Collections.unmodifiableSet(this.supportedGenerics);
   }

}
