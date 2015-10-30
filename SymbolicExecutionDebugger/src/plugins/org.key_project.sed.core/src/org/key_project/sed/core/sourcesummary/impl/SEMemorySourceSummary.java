package org.key_project.sed.core.sourcesummary.impl;

import java.util.LinkedList;
import java.util.List;

import org.key_project.sed.core.sourcesummary.ISESourceSummary;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

/**
 * The default implementation of {@link ISESourceSummary}.
 * @author Martin Hentschel
 */
public class SEMemorySourceSummary implements ISESourceSummary {
   /**
    * The source {@link Object}.
    */
   private final Object source;
   
   /**
    * The contained {@link SEMemorySourceRange}s.
    */
   private final List<SEMemorySourceRange> sourceRanges = new LinkedList<SEMemorySourceRange>();

   /**
    * Constructor.
    * @param source The source {@link Object}.
    */
   public SEMemorySourceSummary(Object source) {
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
   public SEMemorySourceRange[] getSourceRanges() {
      return sourceRanges.toArray(new SEMemorySourceRange[sourceRanges.size()]);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public SEMemorySourceRange getSourceRange(final int lineNumber, final int charStart, final int charEnd) {
      return CollectionUtil.search(sourceRanges, new IFilter<SEMemorySourceRange>() {
         @Override
         public boolean select(SEMemorySourceRange element) {
            return element.getLineNumber() == lineNumber &&
                   element.getCharStart() == charStart &&
                   element.getCharEnd() == charEnd;
         }
      });
   }

   /**
    * Adds the given {@link SEMemorySourceRange}.
    * @param range The {@link SEMemorySourceRange} to add.
    */
   public void addSourceRange(SEMemorySourceRange range) {
      sourceRanges.add(range);
   }
}
