package org.key_project.jmlediting.profile.jmlref.spec_keyword;

import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

/**
 * The requires keyword.
 *
 * @author Moritz Lichter
 *
 */
public class RequiresKeyword extends AbstractGenericSpecificationKeyword {

   /**
    * Creates a new instance for the requires keyword.
    */
   public RequiresKeyword() {
      super("requires");
   }

   @Override
   public String getDescription() {
      return "A requires clause specifies a precondition of method or constructor.";
   }

   @Override
   public IKeywordParser createParser() {
      return new ParseFunctionGenericKeywordParser(NodeTypes.NODE) {

         @Override
         protected ParseFunction createContentParseFunction(
               final IJMLProfile profile) {
            return new ExpressionParser(profile);
         }
      };
   }

}
