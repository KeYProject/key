package de.key_project.jmlediting.profile.jmlref;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

import de.key_project.jmlediting.profile.jmlref.behavior.BehaviorKeyword;
import de.key_project.jmlediting.profile.jmlref.behavior.ExceptionalBehaviorKeyword;
import de.key_project.jmlediting.profile.jmlref.behavior.NormalBehaviorKeyword;
import de.key_project.jmlediting.profile.jmlref.keyword.AssignableKeyword;
import de.key_project.jmlediting.profile.jmlref.keyword.EnsuresKeyword;
import de.key_project.jmlediting.profile.jmlref.keyword.RequiresKeyword;

public class JMLReferenceProfile implements IJMLProfile {

   private static final Set<IKeyword> SUPPORTED_KEYWORDS;

   static {
      Set<IKeyword> supportedKeywords = new HashSet<IKeyword>();
      supportedKeywords.add(new AssignableKeyword());
      supportedKeywords.add(new EnsuresKeyword());
      supportedKeywords.add(new RequiresKeyword());
      supportedKeywords.add(new BehaviorKeyword());
      supportedKeywords.add(new ExceptionalBehaviorKeyword());
      supportedKeywords.add(new NormalBehaviorKeyword());
      SUPPORTED_KEYWORDS = Collections.unmodifiableSet(supportedKeywords);
   }

   public JMLReferenceProfile() {
   }

   @Override
   public String getName() {
      return "JML Reference";
   }

   @Override
   public String getIdentifier() {
      return "org.key_project.jmlediting.profile.jmlref";
   }

   @Override
   public Set<IKeyword> getSupportedKeywords() {
      return SUPPORTED_KEYWORDS;
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

}
