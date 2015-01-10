package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;
import static org.key_project.jmlediting.profile.jmlref.parseutil.JavaBasicsParser.*;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IRecursiveParseFunction;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;

public class ExpressionParser implements ParseFunction {

   @Override
   public IASTNode parse(final String text, final int start, final int end)
         throws ParserException {
      // TODO Auto-generated method stub
      return null;
   }

   // Temporary implementation, will be optimized and moved to another class
   // later on
   // But should cover correct semantics

   private static ParseFunction listOp(final String op, final ParseFunction elem) {
      return listOp(constant(op), elem);
   }

   private static ParseFunction listOp(final ParseFunction op,
         final ParseFunction elem) {
      return seq(elem, list(seq(op, elem)));
   }

   private static ParseFunction brackets(final ParseFunction p) {
      return seq(constant("("), p, constant(")"));
   }

   private static ParseFunction squareBrackets(final ParseFunction p) {
      return seq(constant("["), p, constant("]"));
   }

   private static ParseFunction curlyBrackets(final ParseFunction p) {
      return seq(constant("{"), p, constant("}"));
   }

   private static ParseFunction oneConstant(final String... constants) {
      ParseFunction f = notImplemented();
      for (final String constant : constants) {
         f = alt(constant(constant), f);
      }
      return f;
   }

   public ExpressionParser() {

      // Initially create some parse function which refer recursivly to themself
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
      arrayInitializer.defineAs(curlyBrackets(seq(initializer,
            list(seq(constant(","), initializer)), opt(constant(",")))));
      /**
       * dim-exprs ::= `[' expression `]' [ `[' expression `]' ] ...
       */
      final ParseFunction dimExprs = nonEmptyList(squareBrackets(expression),
            "Expected an expression");

      /**
       * array-decl ::= dim-exprs [ dims ]
       */
      final ParseFunction arrayDecl = seq(dimExprs, opt(dims));

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
      final ParseFunction builtInType = oneConstant("void", "boolean", "byte",
            "char", "short", "int", "long", "float", "double");
      /**
       * reference-type ::= name
       */
      final ParseFunction referenceType = name();
      /**
       * type ::= reference-type | built-in-type
       */
      final ParseFunction type = alt(referenceType, builtInType);
      /**
       * type-spec ::= [ ownership-modifiers ] type [ dims ]<br>
       * | \TYPE [ dims ]
       */
      final ParseFunction ownerShipModifiers = notImplemented(); // C.15
                                                                 // Universe
                                                                 // Type
      // System
      final ParseFunction typeSpec = alt(
            seq(ownerShipModifiers, type, opt(dims)),
            seq(constant("\\TYPE"), opt(dims)));
      /**
       * new-expr ::= new type new-suffix
       */
      final ParseFunction newExpr = seq(constant("new"), type, newSuffix);

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
      final ParseFunction primaryExpr = alt(ident(), newExpr, constant,
            oneConstant("super", "true", "false", "this", "null"),
            brackets(expression), new JMLPrimaryExpressionsParser());

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
      final ParseFunction primarySuffix = alt(seq(
            constant("."),
            alt(ident(),
                  constant("this"),
                  constant("class"),
                  newExpr,
                  seq(constant("super"), brackets(opt(expressionList))),
                  brackets(opt(expressionList)),
                  squareBrackets(expression),
                  seq(list(seq(constant("["), constant("]"))),
                        constant("class")))));

      /**
       * postfix-expr ::= primary-expr [ primary-suffix ] ... [ ++ ]<br>
       * | primary-expr [ primary-suffix ] ... [ -- ]<br>
       * | built-in-type [ `[' `]' ] ... . class
       */
      final ParseFunction postfixExpr = alt(
            seq(primaryExpr, list(primarySuffix), opt(constant("++"))),
            seq(primaryExpr, list(primarySuffix), opt(constant("--"))),
            seq(builtInType, list(seq(constant("["), constant("]"))),
                  constant("."), constant("class")));

      /**
       * unary-expr-not-plus-minus ::= ~ unary-expr<br>
       * | ! unary-expr<br>
       * | ( built-in-type ) unary-expr<br>
       * | ( reference-type ) unary-expr-not-plus-minus<br>
       * | postfix-expr
       */
      final ParseFunction unaryExprNotPlusMinus = alt(
            seq(constant("~"), unaryExpr), seq(constant("!"), unaryExpr),
            seq(brackets(builtInType), unaryExpr),
            seq(brackets(referenceType)), postfixExpr);

      /**
       * unary-expr ::= ( type-spec ) unary-expr<br>
       * | ++ unary-expr<br>
       * | -- unary-expr<br>
       * | + unary-expr<br>
       * | - unary-expr<br>
       * | unary-expr-not-plus-minus
       */
      unaryExpr.defineAs(alt(seq(brackets(typeSpec), unaryExpr),
            seq(constant("++"), unaryExpr), seq(constant("--"), unaryExpr),
            seq(constant("+"), unaryExpr), seq(constant("-"), unaryExpr),
            unaryExprNotPlusMinus));

      /**
       * mult-expr ::= unary-expr [ mult-op unary-expr ] ...<br>
       * mult-op ::= * | / | %
       */
      final ParseFunction multExpr = listOp(unaryExpr,
            oneConstant("*", "/", "%"));

      /**
       * additive-expr ::= mult-expr [ additive-op mult-expr ] ... <br>
       * additive-op ::= + | -
       */
      final ParseFunction additiveExpr = listOp(
            alt(constant("+"), constant("-")), multExpr);

      /**
       * shift-op ::= << | >> | >>>
       */
      final ParseFunction shiftOp = oneConstant("<<", ">>", ">>>");

      /**
       * shift-expr ::= additive-expr [ shift-op additive-expr ] ...
       */
      final ParseFunction shiftExpr = listOp(shiftOp, additiveExpr);

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
      final ParseFunction relationalExpr = alt(
            seq(shiftExpr, relationalExprOp, shiftExpr),
            seq(shiftExpr, opt(seq(constant("instanceof"), typeSpec))));

      /**
       * equality-expr ::= relational-expr [ == relational-expr] ... |
       * relational-expr [ != relational-expr] ...
       */
      final ParseFunction equalityExpr = alt(listOp("==", relationalExpr),
            listOp("!=", relationalExpr));

      /**
       * and-expr ::= equality-expr [ & equality-expr ] ...
       */
      final ParseFunction andExpr = listOp("&", equalityExpr);

      /**
       * exclusive-or-expr ::= and-expr [ ^ and-expr ] ...
       */
      final ParseFunction exclusiveOrExpr = listOp("^", andExpr);

      /**
       * inclusive-or-expr ::= exclusive-or-expr [ `|' exclusive-or-expr ] ...
       */
      final ParseFunction inclusiveOrExpr = listOp("|", exclusiveOrExpr);

      /**
       * logical-and-expr ::= inclusive-or-expr [ && inclusive-or-expr ] ...
       */
      final ParseFunction logicalAndExpr = listOp("&&", inclusiveOrExpr);

      /**
       * logical-or-expr ::= logical-and-expr [ `||' logical-and-expr ] ...
       */
      final ParseFunction logicalOrExpr = listOp("||", logicalAndExpr);

      /**
       * implies-non-backward-expr ::= logical-or-expr <br>
       * [ ==> implies-non-backward-expr ]
       */
      impliesNonBackwardExpr.defineAs(seq(logicalOrExpr,
            opt(seq(constant("==>"), impliesNonBackwardExpr))));

      /**
       * implies-expr ::= <br>
       * logical-or-expr [ ==> implies-non-backward-expr ] <br>
       * | logical-or-expr <== logical-or-expr [ <== logical-or-expr ] ...
       */
      final ParseFunction impliesExpr = alt(
            seq(logicalOrExpr,
                  opt(seq(constant("==>"), impliesNonBackwardExpr))),
            seq(logicalOrExpr, constant("<=="), logicalOrExpr,
                  list(seq(constant("<=="), logicalOrExpr))));

      /**
       * equivalence-op ::= <==> | <=!=>
       */
      final ParseFunction equivalenceOp = oneConstant("<==>", "<=!=>");

      /**
       * equivalence-expr ::= implies-expr [ equivalence-op implies-expr ] ...
       */
      final ParseFunction equivalenceExpr = seq(impliesExpr,
            list(seq(equivalenceOp, impliesExpr)));

      /**
       * conditional-expr ::= equivalence-expr <br>
       * [ ? conditional-expr : conditional-expr ]
       */
      conditionalExpr.defineAs(seq(
            equivalenceExpr,
            opt(seq(constant("?"), conditionalExpr, constant(":"),
                  conditionalExpr))));

      /**
       * assignment-op ::= = | += | -= | *= | /= | %= | >>= | >>>= | <<= | &= |
       * `|=' | ^=
       */
      final ParseFunction assignmentOp = oneConstant("=", "+=", "-=", "*=",
            "/=", "%=", ">>=", ">>>=", "<<=", "&=", "|=", "^=");

      /**
       * assignment-expr ::= conditional-expr [ assignment-op assignment-expr ]
       */
      assignmentExpr.defineAs(seq(conditionalExpr,
            opt(seq(assignmentOp, assignmentExpr))));

      /**
       * expression ::= assignment-expr
       */
      expression.defineAs(assignmentExpr);
      /**
       *
       expression-list ::= expression [ , expression ] ...
       */
      expressionList.defineAs(separatedNonEmptyList(',', expression,
            "Expected an expression"));
   }

}
