package org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression;

import static org.key_project.jmlediting.core.parser.ParserBuilder.*;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.ParseFunction;
import org.key_project.jmlediting.core.parser.ParserException;

public final class ExpressionParserUtils {

   private ExpressionParserUtils() {

   }

   public static ParseFunction listOp(final int type, final String op,
         final ParseFunction elem) {
      return listOp(type, constant(op), elem);
   }

   public static ParseFunction listOp(final int type, final ParseFunction op,
         final ParseFunction elem) {

      final ParseFunction listFunction = list(seq(op, elem));

      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {

            final IASTNode elemResult = elem.parse(text, start, end);

            final IASTNode otherResults = listFunction.parse(text,
                  elemResult.getEndOffset(), end);
            if (otherResults.getChildren().size() == 0) {
               return elemResult;
            }
            final List<IASTNode> opElems = new ArrayList<IASTNode>(otherResults
                  .getChildren().size() * 2 + 1);
            opElems.add(elemResult);
            for (final IASTNode child : otherResults.getChildren()) {
               opElems.addAll(child.getChildren());
            }
            return Nodes.createNode(type, opElems);

         }
      };

   }

   public static ParseFunction repackListOp(final int type,
         final ParseFunction content) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final IASTNode listOptResult = content.parse(text, start, end);

            // System.out.println(listOptResult);
            switch (listOptResult.getChildren().size()) {
            case 0:
            case 1:
               return listOptResult;
            case 2:
               if (listOptResult.getChildren().get(1).getType() == NodeTypes.LIST) {
                  if (listOptResult.getChildren().get(1).getChildren().size() == 0) {
                     return listOptResult.getChildren().get(0);
                  }
               }
               else if (listOptResult.getChildren().get(1).getType() == NodeTypes.NONE) {
                  return listOptResult.getChildren().get(0);
               }
            default:
            }
            final List<IASTNode> opElems = new ArrayList<IASTNode>(
                  listOptResult.getChildren().size() * 2);
            for (final IASTNode child : listOptResult.getChildren()) {
               opElems.addAll(child.getChildren());
            }
            return Nodes.createNode(type, opElems);
         }
      };
   }

   public static ParseFunction unpackOptional(final ParseFunction optional) {
      return new ParseFunction() {

         @Override
         public IASTNode parse(final String text, final int start, final int end)
               throws ParserException {
            final IASTNode optionalNode = optional.parse(text, start, end);
            if (optionalNode.getType() == NodeTypes.SOME) {
               return optionalNode.getChildren().get(0);
            }
            return optionalNode;
         }
      };
   }

}
