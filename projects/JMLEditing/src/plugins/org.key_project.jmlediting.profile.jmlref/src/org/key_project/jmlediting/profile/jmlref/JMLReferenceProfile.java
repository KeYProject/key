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
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AccessibleKeyword;
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

/**
 * Models JML with respect to the JML reference manual.
 * http://www.eecs.ucf.edu/~leavens/JML/jmlrefman/.
 *
 *
 * @author Moritz Lichter
 *
 */
public abstract class JMLReferenceProfile implements IJMLProfile {

   /**
    * A set containing all supported keywords.
    */
   private final Set<IKeyword> supportedKeywords;

   /**
    * Creates a new profile instance with the given supported keyword.
    *
    * @param lang
    *           the keyword locale for AE/BE
    */
   public JMLReferenceProfile(final KeywordLocale lang) {
      this.supportedKeywords = new HashSet<IKeyword>(
            Arrays.asList(new EnsuresKeyword(), new AssignableKeyword(),
                  new AccessibleKeyword(), new RequiresKeyword(),
                  new BehaviorKeyword(lang), new ExceptionalBehaviorKeyword(
                        lang), new NormalBehaviorKeyword(lang),
                        new AlsoKeyword(), new HelperKeyword(), new PureKeyword(),
                        new PrivateKeyword(), new ProtectedKeyword(),
                        new PublicKeyword(), new SpecProtectedKeyword(),
                        new SpecPublicKeyword(), new EverythingKeyword(),
                        new NothingKeyword(), new NotSpecifiedKeyword()));

   }

   @Override
   public final Set<IKeyword> getSupportedKeywords() {
      return Collections.unmodifiableSet(this.supportedKeywords);
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

   /**
    * Returns the modifiable version of the keyword set to allow subclasses to
    * modify them.
    *
    * @return the modifiable keyword set
    */
   protected final Set<IKeyword> getSupportedKeywordsInternal() {
      return this.supportedKeywords;
   }

}
