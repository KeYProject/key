package org.key_project.sed.core.sourcesummary.impl;

import java.util.LinkedList;
import java.util.List;

import org.key_project.sed.core.sourcesummary.ISEDSourceSummary;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

/**
 * The default implementation of {@link ISEDSourceSummary}.
 * @author Martin Hentschel
 */
public class SEDMemorySourceSummary implements ISEDSourceSummary {
   /**
    * The source {@link Object}.
    */
   private final Object source;
   
   /**
    * The contained {@link SEDMemorySourceRange}s.
    */
   private final List<SEDMemorySourceRange> sourceRanges = new LinkedList<SEDMemorySourceRange>();

   /**
    * Constructor.
    * @param source The source {@link Object}.
    */
   public SEDMemorySourceSummary(Object source) {
      this.source = source;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object getSource() {
      return source;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEDMemorySourceRange[] getSourceRanges() {
      return sourceRanges.toArray(new SEDMemorySourceRange[sourceRanges.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEDMemorySourceRange getSourceRange(final int lineNumber, final int charStart, final int charEnd) {
      return CollectionUtil.search(sourceRanges, new IFilter<SEDMemorySourceRange>() {
         @Override
         public boolean select(SEDMemorySourceRange element) {
            return element.getLineNumber() == lineNumber &&
                   element.getCharStart() == charStart &&
                   element.getCharEnd() == charEnd;
         }
      });
   }

   /**
    * Adds the given {@link SEDMemorySourceRange}.
    * @param range The {@link SEDMemorySourceRange} to add.
    */
   public void addSourceRange(SEDMemorySourceRange range) {
      sourceRanges.add(range);
   }
}
