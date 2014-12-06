package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;

public class RequiresKeyword extends AbstractGenericSpecificationKeyword {

   public RequiresKeyword() {
      super("requires");
   }

   @Override
   public String getDescription() {
      return "A requires clause specifies a precondition of method or constructor.";
   }

   @Override
   public IKeywordParser createParser() {
      return new DefaultGenericSpecificationKeywordParser();
   }

}
