package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.core.parser.util.JavaBasicsParser.*;
import static org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes.*;
import static org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionParserUtils.*;

import java.util.Set;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IRecursiveParseFunction;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.type.TypeKeywordSort;

/**
 * The Expression Parser parses expressions as defined in the JML Reference
 * Manual. {@link http
 * ://www.eecs.ucf.edu/~leavens/JML/jmlrefman/jmlrefman_12.html#SEC128}.
 * Currently the following is not implemented: inner classes in JML, set
 * comprehension and owner ship modifiers.
 *
 *
 * @author Moritz Lichter
 *
 */
public class ExpressionParser implements ParseFunction {

   /**
    * The main parser which is used to parse text.
    */
   private final ParseFunction mainParser;

   // Other parse function to publish

   /**
    * The parser for dims.
    */
   private final ParseFunction dimsParser;
   /**
    * The parser for typeSpec.
    */
   private final ParseFunction typeSpecParser;
   private final ParseFunction referenceType;

   private final ParseFunction assignmentExprParser;
   private final ParseFunction exprListParser;
   private final ParseFunction equivalenceExpr;

   /**
    * Returns the parser which parses array dimension declaration.
    *
    * @return the parser for dims
    */
   public ParseFunction dims() {
      return this.dimsParser;
   }

   /**
    * Returns the parser which parses type specifications.
    *
    * @return the type spec parser
    */
   public ParseFunction typeSpec() {
      return this.typeSpecParser;
   }

   /**
    * Returns the parser which parses reference types.
    *
    * @return
    */
   public ParseFunction referenceType() {
      return this.referenceType;
   }

   public ParseFunction assignmentExpr() {
      return this.assignmentExprParser;
   }

   public ParseFunction exprList() {
      return this.exprListParser;
   }

   public ParseFunction equivalenceExpr() {
      return this.equivalenceExpr;
   }

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      return this.mainParser.parse(text, start, end);
   }

   /**
    * Creates a new {@link ExpressionParser} for the given profile. The parser
    * is profile specific because the profile determines the available jml
    * primaries.
    *
    * @param profile
    *           the profile to parse according to
    */
   public ExpressionParser(final IJMLExpressionProfile profile) {

      // Initially create some parse function which refer recursively to
      // themselves
      // It is easy to detect which them, if the function are all declared as
      // local variables. Then all compile errors caused by by referencing a
      // variable
      // before using it, makes the usage of a IRecusiveParseFunction necessary
      // The final modifier is important because the object assigned to the
      // variables
      // is not allowed to change! The objects here can be referred while
      // constructing
      // other parse functions and may be defined calling defineAs() later
      final IRecursiveParseFunction expression = recursiveInit();
      final IRecursiveParseFunction unaryExpr = recursiveInit();
      final IRecursiveParseFunction expressionList = recursiveInit();
      final IRecursiveParseFunction arrayInitializer = recursiveInit();
      final IRecursiveParseFunction conditionalExpr = recursiveInit();
      final IRecursiveParseFunction assignmentExpr = recursiveInit();
      final IRecursiveParseFunction impliesNonBackwardExpr = recursiveInit();
      final IRecursiveParseFunction referenceType = recursiveInit();

      /**
       * dims ::= `[' `]' [ `[' `]' ] ...
       */
      final ParseFunction dims = nonEmptyList(
            seq(constant("["), constant("]")), "Required an [ ]");

      /**
       * initializer ::= expression<br>
       * | array-initializer
       */
      final ParseFunction initializer = alt(expression, arrayInitializer);

      /**
       * array-initializer ::= { [ initializer [ , initializer ] ... [ , ] ] }
       */
      arrayInitializer
            .defineAs(curlyBrackets(seq(ARRAY_INITIALIZER, initializer,
                  list(separateBy(',', initializer)), opt(constant(",")))));
      /**
       * dim-exprs ::= `[' expression `]' [ `[' expression `]' ] ...
       */
      final ParseFunction dimExprs = nonEmptyList(
            squareBrackets(opt(expression)), "Expected an expression");
      /**
       * array-decl ::= dim-exprs [ dims ]
       */
      final ParseFunction arrayDecl = seq(ARRAY_DIM_DECL, dimExprs, opt(dims));

      /**
       * new-suffix ::= ( [ expression-list ] ) [ class-block ]<br>
       * | array-decl [ array-initializer ]<br>
       * | set-comprehension
       */
      final ParseFunction classBlock = notImplemented();
      final ParseFunction setComprehension = notImplemented();
      final ParseFunction newSuffix = alt(
            seq(brackets(opt(expressionList)), opt(classBlock)),
            seq(arrayDecl, opt(arrayInitializer)), setComprehension);

      /**
       * built-in-type ::= void | boolean | byte<br>
       * | char | short | int<br>
       * | long | float | double
       */
      final ParseFunction builtInType = typed(
            PRIMITIVE_TYPE,
            oneConstant("void", "boolean", "byte", "char", "short", "int",
                  "long", "float", "double"));
      /**
       * reference-type ::= name
       */
      // Modified to support generics:
      /**
       * reference-type ::= name [< reference-type >]
       */
      referenceType.defineAs(seq(REFERENCE_TYPE, name(),
            opt(typed(TYPE_ARGUMENT, brackets("<", referenceType, ">")))));

      /**
       * type ::= reference-type | built-in-type
       */
      final ParseFunction type = alt(
            keywords(TypeKeywordSort.INSTANCE, profile), referenceType,
            builtInType);
      /**
       * type-spec ::= [ ownership-modifiers ] type [ dims ]<br>
       * | \TYPE [ dims ]
       */
      final ParseFunction ownerShipModifiers = notImplemented(); // C.15
                                                                 // Universe
                                                                 // Type
      // System
      final ParseFunction typeSpec = alt(
            seq(opt(ownerShipModifiers), type, opt(dims)),
            seq(constant("\\TYPE"), opt(dims)));
      /**
       * new-expr ::= new type new-suffix
       */
      final ParseFunction newExpr = seq(NEW_EXPRESSION,
            typed(JAVA_KEYWORD, constant("new")), type, newSuffix);

      /**
       * constant ::= java-literal
       */
      final ParseFunction constant = javaLiteral();

      /**
       * primary-expr ::= ident | new-expr <br>
       * | constant | super | true<br>
       * | false | this | null<br>
       * | ( expression )<br>
       * | jml-primary
       */
      // Do no include true/false, which is implemented in the constant type
      final ParseFunction jmlPrimary = typed(JML_PRIMARY,
            primary(profile.getSupportedPrimaries(), profile));
      final ParseFunction primaryExpr = alt(typed(IDENTIFIER, ident()),
            newExpr, constant,
            oneConstant(JAVA_KEYWORD, "super", "this", "null"),
            brackets(expression), jmlPrimary);

      /**
       * primary-suffix ::= . ident<br>
       * | . this<br>
       * | . class<br>
       * | . new-expr<br>
       * | . super ( [ expression-list ] )<br>
       * | ( [ expression-list ] )<br>
       * | `[' expression `]'<br>
       * | [ `[' `]' ] ... . class
       */
      final Set<ParseFunction> additionalSuffixes = profile
            .getPrimarySuffixExtensions();
      final ParseFunction primarySuffix = alt(appendFirsts(
            additionalSuffixes,
            seq(MEMBER_ACCESS, constant("."),
                  alt(ident(), constant("this"), constant("class"))),
            seq(constant("."), newExpr),
            seq(SUPER_CALL, constant("."),
                  seq(constant("super"), brackets(opt(expressionList)))),
            typed(METHOD_CALL_PARAMETERS, brackets(opt(expressionList))),
            typed(ARRAY_ACCESS, squareBrackets(expression)),
            seq(ARRAY_CLASS, list(seq(constant("["), constant("]"))),
                  constant("."), constant("class"))));

      /**
       * postfix-expr ::= primary-expr [ primary-suffix ] ... [ ++ ]<br>
       * | primary-expr [ primary-suffix ] ... [ -- ]<br>
       * | built-in-type [ `[' `]' ] ... . class
       */
      final ParseFunction fieldMethodExpr = seq(PRIMARY_EXPR, primaryExpr,
            list(primarySuffix));
      final ParseFunction postfixExpr = alt(
            repackListOp(POST_FIX_EXPR,
                  seq(fieldMethodExpr, opt(oneConstant("++", "--")))),
            seq(ARRAY_CLASS, builtInType,
                  list(seq(constant("["), constant("]"))), constant("."),
                  constant("class")));

      /**
       * unary-expr-not-plus-minus ::= ~ unary-expr<br>
       * | ! unary-expr<br>
       * | ( built-in-type ) unary-expr<br>
       * | ( reference-type ) unary-expr-not-plus-minus<br>
       * | postfix-expr
       */
      final ParseFunction unaryExprNotPlusMinus = alt(
            seq(TILDE, constant("~"), unaryExpr),
            seq(NOT, constant("!"), unaryExpr),
            seq(CAST, brackets(builtInType), unaryExpr),
            seq(CAST, brackets(referenceType)), postfixExpr);

      /**
       * unary-expr ::= ( type-spec ) unary-expr<br>
       * | ++ unary-expr<br>
       * | -- unary-expr<br>
       * | + unary-expr<br>
       * | - unary-expr<br>
       * | unary-expr-not-plus-minus
       */
      unaryExpr.defineAs(alt(seq(CAST, brackets(typeSpec), unaryExpr),
            seq(PREFIX_INCREMENT, constant("++"), unaryExpr),
            seq(PREFIX_DECREMENT, constant("--"), unaryExpr),
            seq(PLUS, constant("+"), unaryExpr),
            seq(MINUS, constant("-"), unaryExpr), unaryExprNotPlusMinus));

      /**
       * mult-expr ::= unary-expr [ mult-op unary-expr ] ...<br>
       * mult-op ::= * | / | %
       */
      final ParseFunction multExpr = listOp(MULT, oneConstant("*", "/", "%"),
            unaryExpr);

      /**
       * additive-expr ::= mult-expr [ additive-op mult-expr ] ... <br>
       * additive-op ::= + | -
       */
      final ParseFunction additiveExpr = listOp(ADDITIVE,
            oneConstant("+", "-"), multExpr);

      /**
       * shift-op ::= << | >> | >>>
       */
      final ParseFunction shiftOp = oneConstant("<<", ">>", ">>>");

      /**
       * shift-expr ::= additive-expr [ shift-op additive-expr ] ...
       */
      final ParseFunction shiftExpr = listOp(SHIFT, shiftOp, additiveExpr);

      /**
       * relational-expr ::= shift-expr < shift-expr <br>
       * | shift-expr > shift-expr <br>
       * | shift-expr <= shift-expr <br>
       * | shift-expr >= shift-expr <br>
       * | shift-expr <: shift-expr <br>
       * | shift-expr [ instanceof type-spec ]
       */
      final ParseFunction relationalExprOp = oneConstant("<", ">", "<=", ">=",
            "<:");
      final ParseFunction relationalExpr = repackListOp(
            RELATIONAL_OP,
            seq(shiftExpr,
                  alt(seq(constant("instanceof"), typeSpec),
                        list(seq(relationalExprOp, shiftExpr)))));

      /**
       * equality-expr ::= relational-expr [ == relational-expr] ... |
       * relational-expr [ != relational-expr] ...
       */
      final ParseFunction equalityExpr = repackListOp(
            EQUALITY,
            seq(relationalExpr,
                  alt(nonEmptyList(seq(constant("=="), relationalExpr), " ss"),
                        list(seq(constant("!="), relationalExpr)))));

      /**
       * and-expr ::= equality-expr [ & equality-expr ] ...
       */
      final ParseFunction andExpr = listOp(BINARY_AND, "&", equalityExpr);

      /**
       * exclusive-or-expr ::= and-expr [ ^ and-expr ] ...
       */
      final ParseFunction exclusiveOrExpr = listOp(BINARY_EXCLUSIVE_OR, "^",
            andExpr);

      /**
       * inclusive-or-expr ::= exclusive-or-expr [ `|' exclusive-or-expr ] ...
       */
      final ParseFunction inclusiveOrExpr = listOp(BINARY_OR, "|",
            exclusiveOrExpr);

      /**
       * logical-and-expr ::= inclusive-or-expr [ && inclusive-or-expr ] ...
       */
      final ParseFunction logicalAndExpr = listOp(LOGICAL_AND, "&&",
            inclusiveOrExpr);

      /**
       * logical-or-expr ::= logical-and-expr [ `||' logical-and-expr ] ...
       */
      final ParseFunction logicalOrExpr = listOp(LOGICAL_OR, "||",
            logicalAndExpr);

      /**
       * implies-non-backward-expr ::= logical-or-expr <br>
       * [ ==> implies-non-backward-expr ]
       */
      impliesNonBackwardExpr.defineAs(repackListOp(
            IMPLIES,
            seq(logicalOrExpr,
                  unpackOptional(opt(seq(constant("==>"),
                        impliesNonBackwardExpr))))));

      /**
       * implies-expr ::= <br>
       * logical-or-expr [ ==> implies-non-backward-expr ] <br>
       * | logical-or-expr <== logical-or-expr [ <== logical-or-expr ] ...
       */
      // Need to switch the order of the alternatives to to restrictions of alt
      // because the ==> may parse a prefix of <==
      // See doc for the alt combinator
      final ParseFunction impliesExpr = repackListOp(
            IMPLIES,
            seq(logicalOrExpr,
                  alt(nonEmptyList(seq(constant("<=="), logicalOrExpr),
                        "Requires another <=="),
                        unpackOptional(opt(seq(constant("==>"),
                              impliesNonBackwardExpr))))));

      /**
       * equivalence-op ::= <==> | <=!=>
       */
      final ParseFunction equivalenceOp = oneConstant("<==>", "<=!=>");

      /**
       * equivalence-expr ::= implies-expr [ equivalence-op implies-expr ] ...
       */
      final ParseFunction equivalenceExpr = listOp(EQUIVALENCE_OP,
            equivalenceOp, impliesExpr);

      /**
       * conditional-expr ::= equivalence-expr-ext <br>
       * [ ? conditional-expr : conditional-expr]
       */
      conditionalExpr.defineAs(repackListOp(
            CONDITIONAL_OP,
            seq(equivalenceExpr,
                  unpackOptional(opt(seq(constant("?"), conditionalExpr,
                        constant(":"), conditionalExpr))))));

      /**
       * assignment-op ::= = | += | -= | *= | /= | %= | >>= | >>>= | <<= | &= |
       * `|=' | ^=
       */
      final ParseFunction assignmentOp = oneConstant("=", "+=", "-=", "*=",
            "/=", "%=", ">>=", ">>>=", "<<=", "&=", "|=", "^=");

      /**
       * assignment-expr ::= conditional-expr [ assignment-op assignment-expr ]
       */
      assignmentExpr
            .defineAs(listOp(ASSIGNMENT, assignmentOp, conditionalExpr));

      /**
       * expression ::= assignment-expr
       */
      expression.defineAs(clean(assignmentExpr));
      /**
       *
       expression-list ::= expression [ , expression ] ...
       */
      expressionList.defineAs(separatedNonEmptyList(EXPRESSION_LIST, ',',
            expression, "Expected an expression"));

      this.mainParser = expression;
      this.dimsParser = dims;
      this.typeSpecParser = typeSpec;
      this.assignmentExprParser = assignmentExpr;
      this.referenceType = referenceType;
      this.exprListParser = expressionList;
      this.equivalenceExpr = equivalenceExpr;
   }
}
