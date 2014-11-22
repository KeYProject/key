package org.key_project.jmlediting.profile.key;

import java.util.Set;

import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IJMLBehaviorKeyword;
import org.key_project.jmlediting.core.profile.syntax.ISpecificationStatementKeyword;

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
   public Set<IJMLBehaviorKeyword> getSupportedBehaviors() {
      // TODO Auto-generated method stub
      return null;
   }

   @Override
   public Set<ISpecificationStatementKeyword> getSupportedGenerics() {
      // TODO Auto-generated method stub
      return null;
   }

}
