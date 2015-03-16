package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.profile.jmlref.IJMLExpressionProfile;
import org.key_project.jmlediting.profile.jmlref.primary.IJMLPrimary;

/**
 * This class contains some utility methods to parse expressions. The declared
 * {@link ParseFunction} are not general enough to put them in another place.
 *
 * @author Moritz Lichter
 *
 */
public final class ExpressionParserUtils {

   /**
    * no instances.
    */
   private ExpressionParserUtils() {

   }

   /**
    * Shorthand for {@link #listOp(int, ParseFunction, ParseFunction)}.
    *
    * @param type
    *           the type of the resulting node
    * @param op
    *           the String, which is token as a constant operator
    * @param elem
    *           the {@link ParseFunction} to parse the elements of the operator
    * @return a {@link ParseFunction} which parses the operator
    */
   public static ParseFunction listOp(final int type, final String op,
         final ParseFunction elem) {
      return listOp(type, constant(op), elem);
   }

   /**
    * Creates a ParseFunction which implements a operator. The operator is
    * parsed by the op {@link ParseFunction}, the elements of the operators by
    * elem according to: elem [op elem] ... <br>
    * . This method implements the same semantic as
    * {@code seq(elem,list(seq(op, elem)))} but produces a nicer AST.
    *
    * @param type
    *           the type of the resulting node
    * @param op
    *           the {@link ParseFunction} to parse the operator
    * @param elem
    *           the {@link ParseFunction} to parse the element
    * @return a {@link ParseFunction} which parses such an operator
    */
   public static ParseFunction listOp(final int type, final ParseFunction op,
         final ParseFunction elem) {

      // This function will be used to parse the list part
      final ParseFunction listFunction = list(seq(op, elem));

      return new ParseFunction() {

         private IASTNode repack(final IASTNode elemResult,
               final IASTNode otherResults) {
            if (otherResults.getChildren().size() == 0) {
               return elemResult;
            }
            // Move the elements from the list into a new node, remove the seq
            // nodes
            final List<IASTNode> opElems = new ArrayList<IASTNode>(otherResults
                  .getChildren().size() * 2 + 1);
            opElems.add(elemResult);
            for (final IASTNode child : otherResults.getChildren()) {
               opElems.addAll(child.getChildren());
            }
            return Nodes.createNode(type, opElems);
         }

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {

            final IASTNode elemResult = elem.parse(text, start, end);

            final IASTNode otherResults = listFunction.parse(text,
                  elemResult.getEndOffset(), end);
            return this.repack(elemResult, otherResults);

         }
      };

   }

   /**
    * Repacks the result of the content function as a result for an operator.
    * That means: If the resulted node x contains two children a and b, this
    * method produces a node of the given type which contains a and all children
    * of all children of b. This is useful to produce a nice AST for operators.
    *
    * @param type
    *           type of the resulting node
    * @param content
    *           a {@link ParseFunction} those result should be repacked
    * @return a {@link ParseFunction} which repacks the result of the given one
    */
   public static ParseFunction repackListOp(final int type,
         final ParseFunction content) {
      return new ParseFunction() {

         /**
          * Performs the repack operation for the given node.
          *
          * @param listOptResult
          *           the node to repack
          * @return the repacked node
          */
         private IASTNode repack(final IASTNode listOptResult) {
            switch (listOptResult.getChildren().size()) {
            case 0:
            case 1:
               // Do not change to node
               return listOptResult;
            case 2:
               final IASTNode firstNode = listOptResult.getChildren().get(0);
               final IASTNode secondNode = listOptResult.getChildren().get(1);
               final int secondNodeType = secondNode.getType();
               // Check whether the second child can be removed, that is the
               // case if it is an empty list or a none
               if (secondNodeType == NodeTypes.LIST) {
                  if (secondNode.getChildren().size() == 0) {
                     return firstNode;
                  }
               }
               else if (secondNodeType == NodeTypes.NONE) {
                  return firstNode;
               }
               // Unpack content depending on the type

               final List<IASTNode> opElems = new ArrayList<IASTNode>(
                     listOptResult.getChildren().size() * 2);
               // First element is not unpacked
               opElems.add(firstNode);

               // But the second one

               if (secondNodeType == NodeTypes.LIST) {
                  for (final IASTNode child : secondNode.getChildren()) {
                     opElems.addAll(child.getChildren());
                  }
               }
               else if (secondNodeType == NodeTypes.SOME) {
                  opElems.addAll(secondNode.getChildren());
               }
               else {
                  opElems.addAll(secondNode.getChildren());
               }
               // Create the new node
               return Nodes.createNode(type, opElems);
            default:
            }
            return listOptResult;

         }

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            // Implement error recovery
            try {
               final IASTNode listOptResult = content.parse(text, start, end);
               return this.repack(listOptResult);
            }
            catch (final ParserException e) {
               if (e.getErrorNode() == null) {
                  throw e;
               }
               else {
                  throw new ParserException(e, this.repack(e.getErrorNode()));
               }
            }

         }
      };
   }

   /**
    * Unpacks the optional result of the given {@link ParseFunction}. If the
    * function returns a Some node, the content of the Some node is returned. A
    * None node is passed untouched.
    *
    * @param optionalFunction
    *           a function which returns a node of type Some or None
    * @return a {@link ParseFunction} which unpacks the Some node
    */
   public static ParseFunction unpackOptional(
         final ParseFunction optionalFunction) {
      return new ParseFunction() {

         /**
          * Unpacks optionalNode if it is a Some node and returns it untouched
          * otherwise
          *
          * @param optionalNode
          *           the node to unpack
          * @return the unpacked node
          */
         private IASTNode unpack(final IASTNode optionalNode) {
            if (optionalNode.getType() == NodeTypes.SOME) {
               return optionalNode.getChildren().get(0);
            }
            return optionalNode;
         }

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            // Support error recovery
            try {
               final IASTNode optionalNode = optionalFunction.parse(text,
                     start, end);
               return this.unpack(optionalNode);
            }
            catch (final ParserException e) {
               if (e.getErrorNode() == null) {
                  throw e;
               }
               else {
                  throw new ParserException(e, this.unpack(e.getErrorNode()));
               }
            }
         }
      };
   }

   /**
    *
    * @param f
    *           the {@link ParseFunction} for the content
    * @return a {@link ParseFunction} which applies {@link #clean(IASTNode)} to
    *         the result of f
    */
   public static ParseFunction clean(final ParseFunction f) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            // Clean with support for error recovery
            try {
               final IASTNode node = f.parse(text, start, end);

               return clean(node);
            }
            catch (final ParserException e) {
               if (e.getErrorNode() == null) {
                  throw e;
               }
               else {
                  throw new ParserException(e, clean(e.getErrorNode()));
               }
            }
         }
      };
   }

   /**
    * Clenas the given AST by removing some parts, which are not interessting.
    * Using this function makes writing the grammar easier and produces a nice
    * AST.
    *
    * @param node
    *           the root node to clean
    * @return a cleaned version of node
    */
   private static IASTNode clean(final IASTNode node) {
      if (node.getStartOffset() == node.getEndOffset()) {
         return null;
      }
      if (node.getChildren().size() == 0) {
         return node;
      }

      final List<IASTNode> children = new ArrayList<IASTNode>();
      for (final IASTNode child : node.getChildren()) {
         final IASTNode cleaned = clean(child);
         if (cleaned != null) {
            children.add(cleaned);
         }
      }
      if (node.getType() == NodeTypes.SEQ && children.size() == 1) {
         return children.get(0);
      }
      if (node.getType() == NodeTypes.SOME) {
         return children.get(0);
      }
      return Nodes.createNode(node.getStartOffset(), node.getEndOffset(),
            node.getType(), children);
   }

   /**
    * Parses a jml primary of the given collection.
    *
    * @param primaries
    *           the supported primaries
    * @param profile
    *           the active profile
    * @return a {@link ParseFunction} parsing {@link IJMLPrimary}
    */
   public static ParseFunction primary(final Collection<IJMLPrimary> primaries,
         final IJMLExpressionProfile profile) {
      return new ParseFunction() {

         private final ParseFunction primary = alt(primaries
               .toArray(new ParseFunction[0]));

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            // Set the profile lazily to allow switching it
            for (final IJMLPrimary primary : primaries) {
               primary.setProfile(profile);
            }
            return this.primary.parse(text, start, end);
         }
      };
   }

   public static ParseFunction[] appendFirsts(
         final Collection<? extends ParseFunction> moreAlts,
         final ParseFunction... alts) {
      final ArrayList<ParseFunction> allFunctions = new ArrayList<ParseFunction>(
            moreAlts.size() + alts.length);
      allFunctions.addAll(Arrays.asList(alts));
      allFunctions.addAll(moreAlts);
      return allFunctions.toArray(new ParseFunction[allFunctions.size()]);
   }

}
