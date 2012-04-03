package org.key_project.sed.ui.visualization.util;

import org.eclipse.graphiti.mm.pictograms.Diagram;

/**
 * Provides static utility methods for Graphiti.
 * @author Martin Hentschel
 */
public final class GraphitiUtil {
   /**
    * Forbid instances.
    */
   private GraphitiUtil() {
   }
   
   /**
    * <p>
    * Computes a size for the given size which snaps to the next grid if
    * {@link Diagram#isSnapToGrid()} is {@code true}. Otherwise the initial
    * size is returned.
    * </p>
    * <p>
    * Example (grid unit = {@code 5}, snap to grid = {@code true}):
    * <pre>
    * nextGrid(diagram, 0) = 0;
    * nextGrid(diagram, 1) = 5;
    * nextGrid(diagram, 2) = 5;
    * nextGrid(diagram, 3) = 5;
    * nextGrid(diagram, 4) = 5;
    * nextGrid(diagram, 5) = 5;
    * </pre>
    * </p>
    * @param targetDiagram The {@link Diagram} to use the size in.
    * @param size The initial size.
    * @return The next size with snap to grid if {@link Diagram#isSnapToGrid()} is {@code true}.
    */
   public static final int nextGrid(Diagram targetDiagram, int size) {
      if (targetDiagram != null && targetDiagram.isSnapToGrid()) {
         int gridUnit = targetDiagram.getGridUnit();
         if (gridUnit != 0) {
            if (gridUnit < 0) {
               gridUnit = gridUnit * -1;
            }
            int divisor = size / gridUnit;
            int rest = size % gridUnit;
            if (rest == 0) {
               return divisor * gridUnit;
            }
            else if (size >= 0) {
               return divisor * gridUnit + gridUnit;      
            }
            else {
               return divisor * gridUnit - gridUnit;      
            }
         }
         else {
            return size;
         }
      }
      else {
         return size;
      }
   }
}
