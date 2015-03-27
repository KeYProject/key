package org.key_project.jmlediting.profile.key.locset;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.ident;

import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.profile.syntax.AbstractKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordParser;
import org.key_project.jmlediting.core.profile.syntax.IKeywordSort;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.bound_mod.BoundVarModifierKeywordSort;
import org.key_project.jmlediting.profile.jmlref.parser.JMLRefParseFunctionKeywordParser;
import org.key_project.jmlediting.profile.jmlref.primary.JMLPrimaryKeywordSort;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParser;

public class InfiniteUnionKeyword extends AbstractKeyword {

   public InfiniteUnionKeyword() {
      super("\\infinite_union");
   }

   @Override
   public String getDescription() {
      return null;
   }

   @Override
   public IKeywordParser createParser() {
      return new JMLRefParseFunctionKeywordParser() {

         @Override
         protected ParseFunction createParseFunction(
               final IJMLExpressionProfile profile) {
            /**
             * \infinite_union ( [bound-var-mod]? type id; [bool-expr ;]
             * loc-set-expr)
             */
            final ParseFunction boundVarMod = keywords(
                  BoundVarModifierKeywordSort.INSTANCE, profile);
            final ExpressionParser expr = new ExpressionParser(profile);
            return brackets(seq(opt(boundVarMod), expr.typeSpec(), ident(),
                  constant(";"), opt(closedBy(NodeTypes.NODE, expr, ';')), expr));
         }
      };
   }

   @Override
   public IKeywordSort getSort() {
      return JMLPrimaryKeywordSort.INSTANCE;
   }

}
