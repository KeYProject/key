package org.key_project.jmlediting.profile.key;

import java.util.Collections;
import java.util.Set;

import org.key_project.jmlediting.core.parser.DefaultJMLParser;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class KeyProfile implements IJMLProfile {

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
      return Collections.emptySet();
   }

   @Override
   public IJMLParser createParser() {
      return new DefaultJMLParser(this);
   }

}
