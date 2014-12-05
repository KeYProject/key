package de.key_project.jmlediting.profile.jmlref;

import java.util.Arrays;
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
import de.key_project.jmlediting.profile.jmlref.other.AlsoKeyword;
import de.key_project.jmlediting.profile.jmlref.other.HelperKeyword;
import de.key_project.jmlediting.profile.jmlref.other.PureKeyword;
import de.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;
import de.key_project.jmlediting.profile.jmlref.spec_keyword.EnsuresKeyword;
import de.key_project.jmlediting.profile.jmlref.spec_keyword.RequiresKeyword;
import de.key_project.jmlediting.profile.jmlref.visibility.PrivateKeyword;
import de.key_project.jmlediting.profile.jmlref.visibility.ProtectedKeyword;
import de.key_project.jmlediting.profile.jmlref.visibility.PublicKeyword;
import de.key_project.jmlediting.profile.jmlref.visibility.SpecProtectedKeyword;
import de.key_project.jmlediting.profile.jmlref.visibility.SpecPublicKeyword;

public class JMLReferenceProfile implements IJMLProfile {

   private static final Set<IKeyword> SUPPORTED_KEYWORDS;

   static {
      final Set<IKeyword> supportedKeywords = new HashSet<IKeyword>(
            Arrays.asList(new AssignableKeyword(), new EnsuresKeyword(),
                  new RequiresKeyword(), new BehaviorKeyword(),
                  new ExceptionalBehaviorKeyword(),
                  new NormalBehaviorKeyword(), new AlsoKeyword(),
                  new HelperKeyword(), new PureKeyword(), new PrivateKeyword(),
                  new ProtectedKeyword(), new PublicKeyword(),
                  new SpecProtectedKeyword(), new SpecPublicKeyword()));

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
