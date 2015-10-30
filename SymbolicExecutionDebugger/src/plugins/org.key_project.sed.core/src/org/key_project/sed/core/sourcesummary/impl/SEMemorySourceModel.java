package org.key_project.sed.core.sourcesummary.impl;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.debug.core.DebugException;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.sourcesummary.ISESourceModel;
import org.key_project.sed.core.util.SEPreorderIterator;

/**
 * The default implementation of {@link ISESourceModel}.
 * @author Martin Hentschel
 */
public class SEMemorySourceModel implements ISESourceModel {
   /**
    * All available {@link SEMemorySourceSummary}s accessible by the source {@link Object}s.
    */
   private final Map<Object, SEMemorySourceSummary> sourceSummaries = new HashMap<Object, SEMemorySourceSummary>();

   /**
    * The parent {@link ISEDebugTarget}.
    */
   private final ISEDebugTarget debugTarget;
   
   /**
    * Indicates that the model is completed or not.
    */
   private boolean possiblyIncomplete = true;

   /**
    * Constructor.
    * @param debugTarget The parent {@link ISEDebugTarget}.
    */
   public SEMemorySourceModel(ISEDebugTarget debugTarget) {
      this.debugTarget = debugTarget;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEMemorySourceSummary[] getSourceSummaries() {
      Collection<SEMemorySourceSummary> values = sourceSummaries.values();
      return values.toArray(new SEMemorySourceSummary[values.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEMemorySourceSummary getSourceSummary(Object source) {
      return sourceSummaries.get(source);
   }

   /**
    * Adds the given {@link SEMemorySourceSummary}.
    * @param summary The {@link SEMemorySourceSummary} to add.
    * @return The previous {@link SEMemorySourceSummary} or {@code null} if no old one was present.
    */
   public SEMemorySourceSummary addSourceSummary(SEMemorySourceSummary summary) {
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
         SEPreorderIterator iterator = new SEPreorderIterator(debugTarget);
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
