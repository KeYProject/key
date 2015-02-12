package org.key_project.sed.ui.text;

import java.util.Collection;
import java.util.HashMap;
import java.util.Map;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.text.Position;
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
    * The {@link ISEDDebugTarget}s with their {@link ISEDSourceRange} in which the code was reached.
    */
   private final Map<ISEDDebugTarget, ISEDSourceRange> targetRanges = new HashMap<ISEDDebugTarget, ISEDSourceRange>();
   
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
    * Checks if at least one {@link ISEDDebugTarget} is available.
    * @return {@code true} has targets, {@code false} has no targets.
    */
   public boolean hasTargets() {
      return !targetRanges.isEmpty();
   }
   
   /**
    * Checks if the given {@link ISEDDebugTarget} is contained in this annotation.
    * @param target The {@link ISEDDebugTarget} to check.
    * @return {@code true} is contained, {@code false} is not contained.
    */
   public boolean containsTarget(ISEDDebugTarget target) {
      return target != null && targetRanges.containsKey(target);
   }
   
   /**
    * Registers the given {@link ISEDDebugTarget} with the given {@link ISEDSourceRange}.
    * @param target The {@link ISEDDebugTarget} to add.
    * @param range The {@link ISEDSourceRange} of the given {@link ISEDDebugTarget}.
    */
   public void setRange(ISEDDebugTarget target, ISEDSourceRange range) {
      if (target != null) {
         targetRanges.put(target, range);
      }
   }
   
   /**
    * Removes the given {@link ISEDDebugTarget}.
    * @param target The {@link ISEDDebugTarget} to remove.
    */
   public void removeTarget(ISEDDebugTarget target) {
      if (target != null) {
         targetRanges.remove(target);
      }
   }
   
   /**
    * Returns the {@link ISEDSourceRange} of the given {@link ISEDDebugTarget} if available.
    * @param target The {@link ISEDDebugTarget} for which the {@link ISEDSourceRange} is requested.
    * @return The {@link ISEDSourceRange} or {@code null} if not available.
    */
   public ISEDSourceRange getRange(ISEDDebugTarget target) {
      return target != null ? targetRanges.get(target) : null;
   }

   /**
    * Returns the specific code range to highlight.
    * @return The specific code range to highlight.
    */
   public ISEDSourceRange[] getRanges() {
      Collection<ISEDSourceRange> values = targetRanges.values();
      return values.toArray(new ISEDSourceRange[values.size()]);
   }

   /**
    * Returns the {@link Position} at which this {@link SymbolicallyReachedAnnotation} is shown.
    * @return The {@link Position} at which this {@link SymbolicallyReachedAnnotation} is shown.
    */
   public Position getPosition() {
      return position;
   }
}
