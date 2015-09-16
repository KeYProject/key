package org.key_project.jmlediting.core.profile;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;
import org.key_project.jmlediting.core.resolver.IResolver;

/**
 * An implementation of {@link IEditableDerivedProfile}.
 *
 * @author Moritz Lichter
 * @param <P>
 *           the type of the parent profile profile
 *
 */
public abstract class DerivedProfile<P extends IJMLProfile> implements
      IDerivedProfile, IEditableDerivedProfile {

   /**
    * The name of the profile.
    */
   private String name;
   /**
    * The constant identifier of the profile.
    */
   private final String identifier;

   /**
    * The constant parent profile of this profile.
    */
   private final P parentProfile;

   private final Set<IKeyword> supportedKeywords;

   /**
    * A set holding all keywords of the parent which are disabled.
    */
   private final Set<IKeyword> disabledParentKeywords;
   /**
    * A set of all keywords, which are supported additionally.
    */
   private final Set<IKeyword> additionalKeywords;
   /**
    * If true, the set of all supported keywords needs to be recalculated. This
    * allows multiple changes to the profile without recalculation the set of
    * all if the set is not requested in the meantime.
    */
   private boolean keywordSetIsDirty;
   
   /**
    * Resolver used by the profile. Can be set using {@link #setResolver(IResolver)}.
    */
   private IResolver resolver;

   /**
    * Creates a new derived profile with the given name and identifier. The
    * profile is derived from the given one.
    *
    * @param name
    *           the name of the profile, not allowed to be null
    * @param identifier
    *           the identifier of the profile, not allowed to be null
    * @param parentProfile
    *           the parent profile, not allowed to be null
    */
   public DerivedProfile(final String identifier, final String name,
         final P parentProfile) {
      super();
      if (identifier == null) {
         throw new IllegalArgumentException(
               "Provide an identifier that is not null");
      }
      if (parentProfile == null) {
         throw new IllegalArgumentException(
               "Provide a parent profile that is not null");
      }
      this.setName(name);
      this.identifier = identifier;
      this.parentProfile = parentProfile;
      this.disabledParentKeywords = new HashSet<IKeyword>();
      this.additionalKeywords = new HashSet<IKeyword>();
      this.keywordSetIsDirty = true;
      this.supportedKeywords = new HashSet<IKeyword>();
      this.recalculateSupportedKeywords();
   }

   @Override
   public String getName() {
      return this.name;
   }

   @Override
   public void setName(final String newName) {
      if (newName == null) {
         throw new IllegalArgumentException("Provide a name which is not null");
      }
      this.name = newName;
   }

   @Override
   public String getIdentifier() {
      return this.identifier;
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

   /**
    * Recalculates the set of all available keywords.
    */
   private void recalculateSupportedKeywords() {
      // Clear old ones
      this.supportedKeywords.clear();
      // Add the keyword of the parent
      this.supportedKeywords.addAll(this.parentProfile.getSupportedKeywords());
      // and remove the disabled ones
      this.supportedKeywords.removeAll(this.disabledParentKeywords);
      // finally add the additonal ones
      this.supportedKeywords.addAll(this.additionalKeywords);
   }

   @Override
   public final Set<IKeyword> getSupportedKeywords() {
      // Check whether the set needs to be recalculated
      if (this.keywordSetIsDirty) {
         this.recalculateSupportedKeywords();
         this.keywordSetIsDirty = false;
      }
      return this.supportedKeywords;
   }

   @Override
   public void setParentKeywordDisabled(final IKeyword parentKeyword,
         final boolean disabled) {
      // Validate that this is a keyword of the parent
      if (!this.parentProfile.getSupportedKeywords().contains(parentKeyword)) {
         throw new IllegalArgumentException(
               "The given keyword is not a keyword of the parent profile");
      }
      // Check whether there is a change
      final boolean change = this.disabledParentKeywords
            .contains(parentKeyword) != disabled;
      if (!change) {
         return;
      }
      // Enable or disable the keyword
      if (disabled) {
         this.disabledParentKeywords.add(parentKeyword);
      }
      else {
         this.disabledParentKeywords.remove(parentKeyword);
      }
      // Calculate new keyword set
      this.keywordSetIsDirty = true;
   }

   @Override
   public void addKeyword(final IKeyword newKeyword) {
      if (newKeyword == null) {
         throw new IllegalArgumentException("Cannot add a null keyword");
      }
      final boolean change = !this.additionalKeywords.contains(newKeyword);
      if (!change) {
         return;
      }
      this.additionalKeywords.add(newKeyword);
      this.keywordSetIsDirty = true;
   }

   @Override
   public void removeKeyword(final IKeyword oldKeyword) {
      if (oldKeyword == null) {
         throw new IllegalArgumentException("Cannot remove a null keyword");
      }
      final boolean change = this.additionalKeywords.contains(oldKeyword);
      if (!change) {
         return;
      }
      this.additionalKeywords.remove(oldKeyword);
      this.keywordSetIsDirty = true;
   }

   @Override
   public P getParentProfile() {
      return this.parentProfile;
   }

   @Override
   public boolean isParentKeywordDisabled(final IKeyword keyword) {
      if (!this.parentProfile.getSupportedKeywords().contains(keyword)) {
         throw new IllegalArgumentException(
               "The keyword is not contained by the parent");
      }
      return this.disabledParentKeywords.contains(keyword);
   }

   @Override
   public Set<IKeyword> getAdditionalKeywords() {
      return Collections.unmodifiableSet(this.additionalKeywords);
   }

   @Override
   public Set<IUserDefinedKeywordContentDescription> getSupportedContentDescriptions() {
      return this.parentProfile.getSupportedContentDescriptions();
   }

   @Override
   public IEditableDerivedProfile derive(final String id, final String name) {
      throw new UnsupportedOperationException(
            "Cannot derive from a derived profile");
   }

   @Override
   public Set<IKeywordSort> getAvailableKeywordSorts() {
      return this.parentProfile.getAvailableKeywordSorts();
   }
   
   @Override
   public IResolver getResolver() {
       return this.resolver;
   }
   
   @Override
   public void setResolver(IResolver newResolver){
       this.resolver = newResolver;
   }
}
