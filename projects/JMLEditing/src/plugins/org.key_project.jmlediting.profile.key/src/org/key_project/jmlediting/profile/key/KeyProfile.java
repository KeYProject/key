package org.key_project.jmlediting.profile.key;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.profile.key.other.StrictlyPureKeyword;

import de.key_project.jmlediting.profile.jmlref.JMLReferenceProfile;

public class KeyProfile extends JMLReferenceProfile {

   private final Set<IKeyword> SUPPORTED_KEYWORDS;

   public KeyProfile() {
      final Set<IKeyword> keywords = new HashSet<IKeyword>(
            super.getSupportedKeywords());
      keywords.add(new StrictlyPureKeyword());
      this.SUPPORTED_KEYWORDS = Collections.unmodifiableSet(keywords);
   }

   @Override
   public String getName() {
      return "Key Profile";
   }

   @Override
   public String getIdentifier() {
      return "org.key_project.jmlediting.profile.key";
   }

   @Override
   public Set<IKeyword> getSupportedKeywords() {
      return this.SUPPORTED_KEYWORDS;
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

}
