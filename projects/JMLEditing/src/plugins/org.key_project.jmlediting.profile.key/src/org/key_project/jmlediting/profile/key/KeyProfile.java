package org.key_project.jmlediting.profile.key;

import java.util.Iterator;
import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserBuilder;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.profile.jmlref.JMLReferenceProfile;
import org.key_project.jmlediting.profile.jmlref.KeywordLocale;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AccessibleKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;
import org.key_project.jmlediting.profile.key.other.InvKeyword;
import org.key_project.jmlediting.profile.key.other.KeyAccessibleKeyword;
import org.key_project.jmlediting.profile.key.other.KeyAssignableKeyword;
import org.key_project.jmlediting.profile.key.other.StrictlyNothingKeyword;
import org.key_project.jmlediting.profile.key.other.StrictlyPureKeyword;

public class KeyProfile extends JMLReferenceProfile {

   public KeyProfile() {
      super(KeywordLocale.AMERICAN);
      // Add strictly keywords
      this.getSupportedKeywordsInternal().add(new StrictlyPureKeyword());
      this.getSupportedKeywordsInternal().add(new StrictlyNothingKeyword());
      // Disable informal descriptions in Assignable/Accessible keywords
      replace(this.getSupportedKeywordsInternal(), AssignableKeyword.class,
            new KeyAssignableKeyword());
      replace(this.getSupportedKeywordsInternal(), AccessibleKeyword.class,
            new KeyAccessibleKeyword());
      this.getSupportedKeywordsInternal().add(new InvKeyword());

      // Allows \inv as access on a not toplevel object just as for x[3].\inv
      this.putExtension(
            ExpressionParser.ADDITIONAL_PRIMARY_SUFFIXES,
            ParserBuilder.separateBy('.',
                  ParserBuilder.keywords(InvKeyword.class, this)),
            ParseFunction.class);
   }

   private static void replace(final Set<IKeyword> keywords,
         final Class<? extends IKeyword> toReplace, final IKeyword keyword) {
      final Iterator<IKeyword> iter = keywords.iterator();
      while (iter.hasNext()) {
         final IKeyword k = iter.next();
         if (k.getClass().equals(toReplace)) {
            iter.remove();
            break;
         }
      }
      keywords.add(keyword);
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
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

}
