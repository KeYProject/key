package org.key_project.sed.core.sourcesummary.impl;

import java.util.LinkedList;
import java.util.List;

import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.sourcesummary.ISEDSourceRange;

/**
 * The default implementation of {@link ISEDSourceRange}.
 * @author Martin Hentschel
 */
public class SEDMemorySourceRange implements ISEDSourceRange {
   /**
    * The line number.
    */
   private final int lineNumber;
   
   /**
    * The index of the start character.
    */
   private final int charStart;
   
   /**
    * The index of the end character.
    */
   private final int charEnd;
   
   /**
    * All {@link ISEDDebugNode}s visiting the specified range.
    */
   private final List<ISEDDebugNode> debugNodes = new LinkedList<ISEDDebugNode>();
   
   /**
    * Constructor.
    * @param lineNumber The line number.
    * @param charStart The index of the start character.
    * @param charEnd The index of the end character.
    */
   public SEDMemorySourceRange(int lineNumber, int charStart, int charEnd) {
      this.lineNumber = lineNumber;
      this.charStart = charStart;
      this.charEnd = charEnd;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getLineNumber() {
      return lineNumber;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharStart() {
      return charStart;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public int getCharEnd() {
      return charEnd;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDDebugNode[] getDebugNodes() {
      return debugNodes.toArray(new ISEDDebugNode[debugNodes.size()]) ;
   }
   
   /**
    * Adds the given {@link ISEDDebugNode}.
    * @param node The {@link ISEDDebugNode} to add.
    */
   public void addDebugNode(ISEDDebugNode node) {
      if (node != null) {
         debugNodes.add(node);
      }
   }
}
