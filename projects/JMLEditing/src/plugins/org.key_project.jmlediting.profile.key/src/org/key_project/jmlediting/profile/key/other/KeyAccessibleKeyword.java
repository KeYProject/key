package org.key_project.jmlediting.profile.key.other;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.AccessibleKeyword;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefKeywordContentParser;

public class KeyAccessibleKeyword extends AccessibleKeyword {
   @Override
   public IKeywordParser createParser() {
      return new StoreRefKeywordContentParser(false);
   }
}
