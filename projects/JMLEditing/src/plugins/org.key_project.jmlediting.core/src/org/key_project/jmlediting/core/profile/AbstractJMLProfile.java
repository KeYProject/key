package org.key_project.jmlediting.core.profile;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.user.EmptyKeywordContent;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;
import org.key_project.jmlediting.core.validation.IJMLValidator;

/**
 * This class implements some methods of the {@link IJMLProfile} in a generic
 * way.
 *
 * @author Moritz Lichter
 *
 */
public abstract class AbstractJMLProfile implements IJMLProfile {

   /**
    * A set containing all supported keywords.
    */
   private final Set<IKeyword> supportedKeywords;

   /**
    * The set containing all keyword content descriptions.
    */
   private final Set<IUserDefinedKeywordContentDescription> supportedContentDescriptions;

   /**
    * Creates a new empty {@link AbstractJMLProfile}.
    */
   public AbstractJMLProfile() {
      this.supportedKeywords = new HashSet<IKeyword>();
      this.supportedContentDescriptions = new HashSet<IUserDefinedKeywordContentDescription>();
      this.supportedContentDescriptions.add(new EmptyKeywordContent());
   }

   @Override
   public Set<IKeyword> getSupportedKeywords() {
      return Collections.unmodifiableSet(this.supportedKeywords);
   }

   @Override
   public Set<IUserDefinedKeywordContentDescription> getSupportedContentDescriptions() {
      return Collections.unmodifiableSet(this.supportedContentDescriptions);
   }

   /**
    * Returns the modifiable version of the keywords set to allow subclasses to
    * access them.
    *
    * @return the modifiable keywords set
    */
   protected final Set<IKeyword> getSupportedKeywordsInternal() {
      return this.supportedKeywords;
   }

   /**
    * Returns the modifiable version of the supported content descriptions set
    * to allow subclasses to access them.
    *
    * @return the modifiable content description set
    */
   protected final Set<IUserDefinedKeywordContentDescription> getSupportedContentDescriptionsInternal() {
      return this.supportedContentDescriptions;
   }

   @Override
   public Set<IJMLValidator> getValidators() {
      return Collections.emptySet();
   }

}
