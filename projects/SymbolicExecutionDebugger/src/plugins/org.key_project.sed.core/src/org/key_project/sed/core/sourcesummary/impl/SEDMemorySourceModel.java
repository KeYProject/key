package org.key_project.sed.core.sourcesummary.impl;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.key_project.sed.core.sourcesummary.ISEDSourceModel;

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
}
