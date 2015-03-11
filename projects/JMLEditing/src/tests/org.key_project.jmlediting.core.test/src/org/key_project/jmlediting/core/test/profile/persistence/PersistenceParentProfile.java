package org.key_project.jmlediting.core.test.profile.persistence;

import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.AbstractJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.AbstractEmptyKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywortSort;
import org.key_project.jmlediting.core.profile.syntax.ToplevelKeywordSort;
import org.key_project.jmlediting.core.profile.syntax.user.EmptyKeywordContent;
import org.key_project.jmlediting.core.profile.syntax.user.IUserDefinedKeywordContentDescription;

public class PersistenceParentProfile extends AbstractJMLProfile {

   public PersistenceParentProfile() {
      final Set<IKeyword> keywords = this.getSupportedKeywordsInternal();
      keywords.add(new AbstractEmptyKeyword("keyword1") {

         @Override
         public IKeywortSort getSort() {
            return ToplevelKeywordSort.INSTANCE;
         }

         @Override
         public String getDescription() {
            return null;
         }
      });
      final Set<IUserDefinedKeywordContentDescription> descr = this
            .getSupportedContentDescriptionsInternal();
      descr.add(new EmptyKeywordContent());
   }

   @Override
   public String getName() {
      return "Persistence Parent";
   }

   @Override
   public String getIdentifier() {
      return this.getClass().getName();
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

}
