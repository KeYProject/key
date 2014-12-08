package org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref;

import static org.key_project.jmlediting.core.parser.ParserUtils.*;
import static org.key_project.jmlediting.profile.jmlref.spec_keyword.storeref.StoreRefNodeTypes.*;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.parser.ParserUtils.MutableContainer;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;

public class StoreRefParser implements ParseFunction {

   // These two containers are used to bring state into the store ref parser:
   // the knowledge about the profile and the enabled
   // StoreRefKeywords in it
   // Using these containers allows to initialize the parse function inline and
   // not in the constructor which makes the parser much more
   // readable

   private final MutableContainer<List<IStoreRefKeyword>> storeRefKeywords = new MutableContainer<List<IStoreRefKeyword>>();
   private final MutableContainer<IJMLProfile> profile = new MutableContainer<IJMLProfile>();

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.storeRefList.parse(text, start, end);
   }

   public StoreRefParser(final IJMLProfile profile) {
      this.profile.set(profile);
      final List<IStoreRefKeyword> storeRefKeywordsList = new ArrayList<IStoreRefKeyword>();
      for (final IKeyword k : profile.getSupportedKeywords()) {
         if (k instanceof IStoreRefKeyword) {
            storeRefKeywordsList.add((IStoreRefKeyword) k);
         }
      }
      this.storeRefKeywords.set(storeRefKeywordsList);

   }

   // The list if filled by the constructor because the content is profile
   // sensitive
   /**
    * store-ref-keyword ::= \nothing | \everything | \not_specified
    *
    */
   @SuppressWarnings("unchecked")
   private final ParseFunction storeRefKeyword = parseKeyword(
         this.storeRefKeywords, this.profile);

   private final ParseFunction specExpression = integerConstant();

   /**
    * spec-array-ref-expr ::= spec-expression <br>
    * | spec-expression .. spec-expression <br>
    * | *
    *
    * Need to try the second case before the first case because otherwise we
    * will never parse it
    *
    */
   private final ParseFunction specArrayRefExpression = alternative(
         seq(this.specExpression, constant(".."), this.specExpression),
         this.specExpression, constant("*"));

   /**
    * store-ref-name-suffix ::= . ident <br>
    * | . this <br>
    * | `[' spec-array-ref-expr `]' <br>
    * | . *
    *
    */
   private final ParseFunction storeRefNameSuffix = typed(
         STORE_REF_NAME_SUFFIX,
         alternative(separateBy('.', identifier()),
               separateBy('.', constant("*")),
               seq(constant("["), this.specArrayRefExpression, constant("]"))));
   /**
    * store-ref-name ::= ident | super | this
    *
    * Approximates and does not check for keywords, because they are treated as
    * identifiers
    */
   private final ParseFunction storeRefName = identifier();

   /**
    * store-ref-expression ::= store-ref-name [ store-ref-name-suffix ] ...
    */
   private final ParseFunction storeRefExpr = seq(STORE_REF_EXPR,
         this.storeRefName, parseList(this.storeRefNameSuffix));

   private final ParseFunction informalExpr = notImplemented();

   /**
    * store-ref ::= store-ref-expression <br>
    * | informal-description
    */
   private final ParseFunction storeRef = alternative(this.storeRefExpr,
         this.informalExpr);

   /**
    * store-ref-list ::= store-ref-keyword <br>
    * | store-ref [ , store-ref ] ... Wrap the keyword in a list, to unify the
    * AST
    */
   private final ParseFunction storeRefList = typed(
         STORE_REF_LIST,
         alternative(
               this.storeRefKeyword,
               parseSeparatedNonEmptyList(',', this.storeRef,
                     "Expected at least one storage reference")));

}
