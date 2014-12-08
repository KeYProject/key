package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AssignableKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordContentParser;

public class KeyAssignableKeyword extends AssignableKeyword {

   @Override
   public IKeywordParser createParser() {
      return new StoreRefKeywordContentParser(false);
   }
}
