package org.key_project.jmlediting.profile.jmlref;

import java.util.Arrays;
import java.util.Collections;
import java.util.HashSet;
import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.profile.jmlref.behavior.BehaviorKeyword;
import org.key_project.jmlediting.profile.jmlref.behavior.ExceptionalBehaviorKeyword;
import org.key_project.jmlediting.profile.jmlref.behavior.NormalBehaviorKeyword;
import org.key_project.jmlediting.profile.jmlref.other.AlsoKeyword;
import org.key_project.jmlediting.profile.jmlref.other.HelperKeyword;
import org.key_project.jmlediting.profile.jmlref.other.PureKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.EnsuresKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.RequiresKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.EverythingKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.NotSpecifiedKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.NothingKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.PrivateKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.ProtectedKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.PublicKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.SpecProtectedKeyword;
import org.key_project.jmlediting.profile.jmlref.visibility.SpecPublicKeyword;

public class JMLReferenceProfile implements IJMLProfile {

   private final Set<IKeyword> SUPPORTED_KEYWORDS;

   public JMLReferenceProfile() {
      final Set<IKeyword> supportedKeywords = new HashSet<IKeyword>(
            Arrays.asList(new EnsuresKeyword(), new AssignableKeyword(),
                  new RequiresKeyword(), new BehaviorKeyword(),
                  new ExceptionalBehaviorKeyword(),
                  new NormalBehaviorKeyword(), new AlsoKeyword(),
                  new HelperKeyword(), new PureKeyword(), new PrivateKeyword(),
                  new ProtectedKeyword(), new PublicKeyword(),
                  new SpecProtectedKeyword(), new SpecPublicKeyword(),
                  new EverythingKeyword(), new NothingKeyword(),
                  new NotSpecifiedKeyword()));

      this.SUPPORTED_KEYWORDS = Collections.unmodifiableSet(supportedKeywords);
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
      return this.SUPPORTED_KEYWORDS;
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

}
