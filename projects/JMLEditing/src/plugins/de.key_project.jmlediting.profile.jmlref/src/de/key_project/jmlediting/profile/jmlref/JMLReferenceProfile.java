package de.key_project.jmlediting.profile.jmlref;

import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

import de.key_project.jmlediting.profile.jmlref.behavior.BehaviorKeyword;
import de.key_project.jmlediting.profile.jmlref.behavior.ExceptionalBehaviorKeyword;
import de.key_project.jmlediting.profile.jmlref.behavior.NormalBehaviorKeyword;
import de.key_project.jmlediting.profile.jmlref.keyword.AssignableKeyword;
import de.key_project.jmlediting.profile.jmlref.keyword.EnsuresKeyword;
import de.key_project.jmlediting.profile.jmlref.keyword.RequiresKeyword;

public class JMLReferenceProfile implements IJMLProfile {
   
   private static final Set<ISpecificationStatementKeyword> SUPPORTED_KEYWORDS;
   private static final Set<IJMLBehaviorKeyword> SUPPORTED_BEHAVIOR_KEYWORDS; 
   
   static {
      Set<ISpecificationStatementKeyword> supportedKeywords = new HashSet<ISpecificationStatementKeyword>();
      supportedKeywords.add(new AssignableKeyword());
      supportedKeywords.add(new EnsuresKeyword());
      supportedKeywords.add(new RequiresKeyword());
      SUPPORTED_KEYWORDS = Collections.unmodifiableSet(supportedKeywords);
      
      Set<IJMLBehaviorKeyword> supportedBehaviorKeywords = new HashSet<IJMLBehaviorKeyword>();
      supportedBehaviorKeywords.add(new BehaviorKeyword());
      supportedBehaviorKeywords.add(new ExceptionalBehaviorKeyword());
      supportedBehaviorKeywords.add(new NormalBehaviorKeyword());
      SUPPORTED_BEHAVIOR_KEYWORDS = Collections.unmodifiableSet(supportedBehaviorKeywords);
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
   public Set<IJMLBehaviorKeyword> getSupportedBehaviors() {
      return SUPPORTED_BEHAVIOR_KEYWORDS;
   }

   @Override
   public Set<ISpecificationStatementKeyword> getSupportedSpecificationStatementKeywords() {
      return SUPPORTED_KEYWORDS;
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

}
