package org.key_project.sed.ui.text;

import org.eclipse.jface.text.source.Annotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.sourcesummary.ISEDSourceRange;

/**
 * An {@link Annotation} highlighting code reached during symbolic execution.
 * @author Martin Hentschel
 */
public class SymbolicallyReachedAnnotation extends Annotation {
   /**
    * The ID of this {@link Annotation}.
    */
   public static final String TYPE = "org.key_project.sed.ui.SymbolicallyReachedAnnotation";
   
   /**
    * The {@link ISEDDebugTarget} in which the code was reached.
    */
   private final ISEDDebugTarget target;
   
   /**
    * The specific code range to highlight.
    */
   private final ISEDSourceRange range;
   
   /**
    * Constructor.
    * @param target The {@link ISEDDebugTarget} in which the code was reached.
    * @param range The specific code range to highlight.
    */
   public SymbolicallyReachedAnnotation(ISEDDebugTarget target, ISEDSourceRange range) {
      super(TYPE, false, "Symbolically Reached");
      this.target = target;
      this.range = range;
   }

   /**
    * Returns the {@link ISEDDebugTarget} in which the code was reached.
    * @return The {@link ISEDDebugTarget} in which the code was reached.
    */
   public ISEDDebugTarget getTarget() {
      return target;
   }

   /**
    * Returns the specific code range to highlight.
    * @return The specific code range to highlight.
    */
   public ISEDSourceRange getRange() {
      return range;
   }
}
