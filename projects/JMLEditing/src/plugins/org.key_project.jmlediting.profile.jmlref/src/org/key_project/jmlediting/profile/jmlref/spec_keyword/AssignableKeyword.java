package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.parser.ParserUtils;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefParser;

public class AssignableKeyword extends AbstractGenericSpecificationKeyword {

   public AssignableKeyword() {
      super("assignable");
   }

   @Override
   public String getDescription() {
      return "An assignable clause gives a frame axiom for a specification. It says that, from the client's point of view, only the locations named, and locations in the data groups associated with these locations, can be assigned to during the execution of the method. The values of all subexpressions used in assignable clauses, such as i-1 in a[i-1], are computed in the pre-state of the method, because the assignable clause only talks about locations that exist in the pre-state.";
   }

   @Override
   public IKeywordParser createParser() {
      return new AbstractGenericSpecificationKeywordParser() {

         private StoreRefParser parser;

         @Override
         public void setProfile(final IJMLProfile profile) {
            this.parser = new StoreRefParser(profile);
         }

         @Override
         protected IASTNode parseToSemicolon(final String text,
               final int start, final int end) throws ParserException {
            return ParserUtils.requireComplete(this.parser).parse(text, start,
                  end);
         }

      };
   }

}
