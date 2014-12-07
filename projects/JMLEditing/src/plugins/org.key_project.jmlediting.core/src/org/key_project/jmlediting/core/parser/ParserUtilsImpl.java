package org.key_project.jmlediting.core.parser;

import java.util.ArrayList;
import java.util.List;

import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;

public class ParserUtilsImpl {

   static List<IASTNode> parseListImpl(final String text, final int start,
         final int end, final ParseFunction function) {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();

      int startPosition = start;
      while (true) {
         try {
            final IASTNode listNode = function.parse(text, startPosition, end);
            nodes.add(listNode);
            startPosition = listNode.getEndOffset();
         }
         catch (final ParserException e) {
            break;
         }
      }
      return nodes;
   }

   static IASTNode parseSeparatedList(final String text, final int start,
         final int end, final char sep, final ParseFunction function) {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();
      try {
         final IASTNode node = function.parse(text, start, end);
         nodes.add(node);
      }
      catch (final ParserException e) {
         return Nodes.createNode(start, start, NodeTypes.LIST);
      }
      final ParseFunction sepFunction = ParserUtils.separateBy(sep, function);
      while (true) {
         try {
            final IASTNode listNode = sepFunction.parse(text, start, end);
            nodes.add(listNode);
         }
         catch (final ParserException e) {
            break;
         }
      }
      return Nodes.createNode(NodeTypes.LIST, nodes);
   }

   static IASTNode parseSeparatedNonEmptyList(final String text,
         final int start, final int end, final char sep,
         final ParseFunction function, final String missingExceptionText)
         throws ParserException {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();
      try {
         final IASTNode node = function.parse(text, start, end);
         nodes.add(node);
      }
      catch (final ParserException e) {
         throw new ParserException(missingExceptionText, text, start, e);
      }
      final ParseFunction sepFunction = ParserUtils.separateBy(sep, function);
      while (true) {
         try {
            final IASTNode listNode = sepFunction.parse(text, start, end);
            nodes.add(listNode);
         }
         catch (final ParserException e) {
            break;
         }
      }
      return Nodes.createNode(NodeTypes.LIST, nodes);
   }

   public static IASTNode parseList(final String text, final int start,
         final int end, final ParseFunction function) {
      final List<IASTNode> nodes = parseListImpl(text, start, end, function);
      if (nodes.isEmpty()) {
         return Nodes.createNode(start, start, NodeTypes.LIST);
      }
      else {
         return Nodes.createNode(NodeTypes.LIST, nodes);
      }
   }

   public static IASTNode parseNonEmptyList(final String text, final int start,
         final int end, final ParseFunction function,
         final String missingExceptionText) throws ParserException {
      final List<IASTNode> nodes = parseListImpl(text, start, end, function);
      if (nodes.isEmpty()) {
         throw new ParserException(missingExceptionText, text, start);
      }
      return Nodes.createNode(NodeTypes.LIST, nodes);
   }

   public static IASTNode parseSeq(final int type, final String text,
         final int start, final int end, final ParseFunction... seqs)
               throws ParserException {
      final List<IASTNode> nodes = new ArrayList<IASTNode>();
      int startPosition = start;
      for (final ParseFunction function : seqs) {
         final IASTNode node = function.parse(text, startPosition, end);
         nodes.add(node);
         startPosition = node.getEndOffset();
      }
      assert (nodes.size() == seqs.length);
      return Nodes.createNode(type, nodes);
   }

   public static IASTNode parseAlternative(final String text, final int start,
         final int end, final ParseFunction... alternatives)
               throws ParserException {
      ParserException exception = null;
      for (final ParseFunction function : alternatives) {
         try {
            return function.parse(text, start, end);
         }
         catch (final ParserException e) {
            exception = e;
         }
      }
      throw exception;
   }

}
