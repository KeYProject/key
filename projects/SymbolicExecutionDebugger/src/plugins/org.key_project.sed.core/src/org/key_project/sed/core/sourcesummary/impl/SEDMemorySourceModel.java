package org.key_project.sed.core.sourcesummary.impl;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.sourcesummary.ISEDSourceModel;
import org.key_project.sed.core.util.SEDPreorderIterator;

/**
 * The default implementation of {@link ISEDSourceModel}.
 * @author Martin Hentschel
 */
public class SEDMemorySourceModel implements ISEDSourceModel {
   /**
    * All available {@link SEDMemorySourceSummary}s accessible by the source {@link Object}s.
    */
   private final Map<Object, SEDMemorySourceSummary> sourceSummaries = new HashMap<Object, SEDMemorySourceSummary>();

   /**
    * The parent {@link ISEDDebugTarget}.
    */
   private final ISEDDebugTarget debugTarget;
   
   /**
    * Indicates that the model is completed or not.
    */
   private boolean possiblyIncomplete = true;

   /**
    * Constructor.
    * @param debugTarget The parent {@link ISEDDebugTarget}.
    */
   public SEDMemorySourceModel(ISEDDebugTarget debugTarget) {
      this.debugTarget = debugTarget;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEDMemorySourceSummary[] getSourceSummaries() {
      Collection<SEDMemorySourceSummary> values = sourceSummaries.values();
      return values.toArray(new SEDMemorySourceSummary[values.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEDMemorySourceSummary getSourceSummary(Object source) {
      return sourceSummaries.get(source);
   }

   /**
    * Adds the given {@link SEDMemorySourceSummary}.
    * @param summary The {@link SEDMemorySourceSummary} to add.
    * @return The previous {@link SEDMemorySourceSummary} or {@code null} if no old one was present.
    */
   public SEDMemorySourceSummary addSourceSummary(SEDMemorySourceSummary summary) {
      if (summary != null) {
         return sourceSummaries.put(summary.getSource(), summary);
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void ensureCompleteness() throws DebugException {
      if (possiblyIncomplete) {
         // Iterate over the full tree to ensure that all nodes are loaded.
         SEDPreorderIterator iterator = new SEDPreorderIterator(debugTarget);
         while (iterator.hasNext()) {
            iterator.next();
         }
         this.possiblyIncomplete = false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setPossiblyIncomplete() {
      this.possiblyIncomplete = true;
   }
}
