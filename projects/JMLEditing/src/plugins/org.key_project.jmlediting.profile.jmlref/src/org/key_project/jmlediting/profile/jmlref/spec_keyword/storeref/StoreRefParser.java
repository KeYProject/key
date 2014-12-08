package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import static org.key_project.jmlediting.core.parser.ParserUtils.*;
import static org.key_project.jmlediting.profile.jmlref.parseutil.Lexicals.lexInformalDescr;
import static org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefNodeTypes.*;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class StoreRefParser implements ParseFunction {

   private final ParseFunction mainParser;

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.mainParser.parse(text, start, end);
   }

   public StoreRefParser(final IJMLProfile profile,
         final boolean allowInformalDescription) {
      final List<IStoreRefKeyword> storeRefKeywords = new ArrayList<IStoreRefKeyword>();
      for (final IKeyword k : profile.getSupportedKeywords()) {
         if (k instanceof IStoreRefKeyword) {
            storeRefKeywords.add((IStoreRefKeyword) k);
         }
      }

      // The list if filled by the constructor because the content is profile
      // sensitive
      /*
       * store-ref-keyword ::= \nothing | \everything | \not_specified
       */
      final ParseFunction storeRefKeyword = parseKeyword(storeRefKeywords,
            profile);

      final ParseFunction specExpression = integerConstant();

      /*
       * spec-array-ref-expr ::= spec-expression <br> | spec-expression ..
       * spec-expression <br> | *
       * 
       * Need to try the second case before the first case because otherwise we
       * will never parse it
       */
      final ParseFunction specArrayRefExpression = alternative(
            seq(specExpression, constant(".."), specExpression),
            specExpression, constant("*"));

      /*
       * store-ref-name-suffix ::= . ident <br> | . this <br> | `['
       * spec-array-ref-expr `]' <br> | . *
       */
      final ParseFunction storeRefNameSuffix = typed(
            STORE_REF_NAME_SUFFIX,
            alternative(separateBy('.', identifier()),
                  separateBy('.', constant("*")),
                  seq(constant("["), specArrayRefExpression, constant("]"))));
      /*
       * store-ref-name ::= ident | super | this
       * 
       * Approximates and does not check for keywords, because they are treated
       * as identifiers
       */
      final ParseFunction storeRefName = identifier();

      /*
       * store-ref-expression ::= store-ref-name [ store-ref-name-suffix ] ...
       */
      final ParseFunction storeRefExpr = seq(STORE_REF_EXPR, storeRefName,
            parseList(storeRefNameSuffix));

      // Make lexInformalDesc context free
      final ParseFunction informalDescr = allowWhitespace(lexInformalDescr);

      /*
       * store-ref ::= store-ref-expression <br> | informal-description <br>
       * Informal descriptions may be disabled
       */
      final ParseFunction storeRef;
      if (allowInformalDescription) {
         storeRef = alternative(storeRefExpr, informalDescr);
      }
      else {
         storeRef = storeRefExpr;
      }

      /*
       * store-ref-list ::= store-ref-keyword <br> | store-ref [ , store-ref ]
       * ... Wrap the keyword in a list, to unify the AST
       */
      final ParseFunction storeRefList = typed(
            STORE_REF_LIST,
            alternative(
                  storeRefKeyword,
                  parseSeparatedNonEmptyList(',', storeRef,
                        "Expected at least one storage reference")));

      this.mainParser = storeRefList;
   }

}
