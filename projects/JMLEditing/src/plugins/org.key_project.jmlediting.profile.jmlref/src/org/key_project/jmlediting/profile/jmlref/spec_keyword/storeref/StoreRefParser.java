package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import static org.key_project.jmlediting.core.parser.ParserUtils.*;
import static org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefNodeTypes.*;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;

public class StoreRefParser implements ParseFunction {

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return storeRefList.parse(text, start, end);
   }

   private static final ParseFunction storeRefKeyword = notImplemented();

   private static final ParseFunction specExpression = integerConstant();

   /**
    * spec-array-ref-expr ::= spec-expression <br>
    * | spec-expression .. spec-expression <br>
    * | *
    *
    * Need to try the second case before the first case because otherwise we
    * will never parse it
    *
    */
   private static final ParseFunction specArrayRefExpression = alternative(
         seq(specExpression, constant(".."), specExpression), specExpression,
         constant("*"));

   /**
    * store-ref-name-suffix ::= . ident <br>
    * | . this <br>
    * | `[' spec-array-ref-expr `]' <br>
    * | . *
    *
    */
   private static ParseFunction storeRefNameSuffix = typed(
         STORE_REF_NAME_SUFFIX,
         alternative(separateBy('.', identifier()),
               separateBy('.', constant("*")),
               seq(constant("["), specArrayRefExpression, constant("]"))));
   /**
    * store-ref-name ::= ident | super | this
    *
    * Approximates and does not check for keywords, because they are treated as
    * identifiers
    */
   private static final ParseFunction storeRefName = identifier();

   /**
    * store-ref-expression ::= store-ref-name [ store-ref-name-suffix ] ...
    */
   private static final ParseFunction storeRefExpr = seq(STORE_REF_EXPR,
         storeRefName, parseList(storeRefNameSuffix));

   private static final ParseFunction informalExpr = notImplemented();

   /**
    * store-ref ::= store-ref-expression <br>
    * | informal-description
    */
   private static final ParseFunction storeRef = alternative(storeRefExpr,
         informalExpr);

   /**
    * store-ref-list ::= store-ref-keyword <br>
    * | store-ref [ , store-ref ] ...
    *
    */
   private static final ParseFunction storeRefList = alternative(
         storeRefKeyword,
         parseSeparatedNonEmptyList(',', storeRef,
               "Expected at least one storage reference"));

}
