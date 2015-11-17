package org.key_project.sed.ui.text;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.Position;
import org.eclipse.jface.text.source.Annotation;
import org.key_project.sed.core.model.ISEDebugTarget;
import org.key_project.sed.core.sourcesummary.ISESourceRange;

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
    * The {@link ISEDebugTarget}s with their {@link ISESourceRange} in which the code was reached.
    */
   private final Map<ISEDebugTarget, ISESourceRange> targetRanges = new HashMap<ISEDebugTarget, ISESourceRange>();
   
   /**
    * The {@link Position} at which this {@link SymbolicallyReachedAnnotation} is shown.
    */
   private final Position position;
   
   /**
    * Constructor.
    */
   public SymbolicallyReachedAnnotation(Position position) {
      super(TYPE, false, "Symbolically Reached");
      Assert.isNotNull(position);
      this.position = position;
   }
   
   /**
    * Checks if at least one {@link ISEDebugTarget} is available.
    * @return {@code true} has targets, {@code false} has no targets.
    */
   public boolean hasTargets() {
      return !targetRanges.isEmpty();
   }
   
   /**
    * Checks if the given {@link ISEDebugTarget} is contained in this annotation.
    * @param target The {@link ISEDebugTarget} to check.
    * @return {@code true} is contained, {@code false} is not contained.
    */
   public boolean containsTarget(ISEDebugTarget target) {
      return target != null && targetRanges.containsKey(target);
   }
   
   /**
    * Registers the given {@link ISEDebugTarget} with the given {@link ISESourceRange}.
    * @param target The {@link ISEDebugTarget} to add.
    * @param range The {@link ISESourceRange} of the given {@link ISEDebugTarget}.
    */
   public void setRange(ISEDebugTarget target, ISESourceRange range) {
      if (target != null) {
         targetRanges.put(target, range);
      }
   }
   
   /**
    * Removes the given {@link ISEDebugTarget}.
    * @param target The {@link ISEDebugTarget} to remove.
    */
   public void removeTarget(ISEDebugTarget target) {
      if (target != null) {
         targetRanges.remove(target);
      }
   }
   
   /**
    * Returns the {@link ISESourceRange} of the given {@link ISEDebugTarget} if available.
    * @param target The {@link ISEDebugTarget} for which the {@link ISESourceRange} is requested.
    * @return The {@link ISESourceRange} or {@code null} if not available.
    */
   public ISESourceRange getRange(ISEDebugTarget target) {
      return target != null ? targetRanges.get(target) : null;
   }

   /**
    * Returns the specific code range to highlight.
    * @return The specific code range to highlight.
    */
   public ISESourceRange[] getRanges() {
      Collection<ISESourceRange> values = targetRanges.values();
      return values.toArray(new ISESourceRange[values.size()]);
   }

   /**
    * Returns the {@link Position} at which this {@link SymbolicallyReachedAnnotation} is shown.
    * @return The {@link Position} at which this {@link SymbolicallyReachedAnnotation} is shown.
    */
   public Position getPosition() {
      return position;
   }
}
