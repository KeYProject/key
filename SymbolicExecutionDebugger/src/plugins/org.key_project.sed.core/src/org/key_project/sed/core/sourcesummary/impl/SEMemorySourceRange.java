package org.key_project.sed.core.sourcesummary.impl;

import java.util.LinkedList;
import java.util.List;

import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.sourcesummary.ISESourceRange;

/**
 * The default implementation of {@link ISESourceRange}.
 * @author Martin Hentschel
 */
public class SEMemorySourceRange implements ISESourceRange {
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
    * All {@link ISENode}s visiting the specified range.
    */
   private final List<ISENode> debugNodes = new LinkedList<ISENode>();
   
   /**
    * Constructor.
    * @param lineNumber The line number.
    * @param charStart The index of the start character.
    * @param charEnd The index of the end character.
    */
   public SEMemorySourceRange(int lineNumber, int charStart, int charEnd) {
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
   public ISENode[] getDebugNodes() {
      return debugNodes.toArray(new ISENode[debugNodes.size()]) ;
   }
   
   /**
    * Adds the given {@link ISENode}.
    * @param node The {@link ISENode} to add.
    */
   public void addDebugNode(ISENode node) {
      if (node != null) {
         debugNodes.add(node);
      }
   }
}
