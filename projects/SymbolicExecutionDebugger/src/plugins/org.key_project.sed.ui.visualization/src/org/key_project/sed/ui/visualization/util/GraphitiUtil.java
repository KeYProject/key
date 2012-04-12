package org.key_project.sed.ui.visualization.util;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.editor.DiagramEditorInput;

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
   
   /**
    * Returns the {@link IFile} which is specified by the given {@link DiagramEditorInput}
    * if available.
    * @param input The {@link DiagramEditorInput}.
    * @return The specified {@link IFile} or {@code null} if no {@link IFile} is specified.
    */
   public static IFile getFile(DiagramEditorInput input) {
      IFile result = null;
      if (input != null) {
         EObject obj = input.getEObject();
         if (obj != null) {
            result = getFile(obj);
         }
      }
      return result;
   }
   
   /**
    * Returns the {@link IFile} which is specified by the given {@link DiagramEditorInput}
    * if available.
    * @param input The {@link DiagramEditorInput}.
    * @return The specified {@link IFile} or {@code null} if no {@link IFile} is specified.
    */
   public static IFile getFile(EObject obj) {
      IFile result = null;
      if (obj != null) {
         Resource resource = obj.eResource();
         if (resource != null) {
            URI uri = resource.getURI();
            if (uri.isPlatformResource()) {
               result = ResourcesPlugin.getWorkspace().getRoot().getFile(new Path(uri.toPlatformString(true)));
            }
         }
      }
      return result;
   }
   
   /**
    * Returns all contained {@link PictogramElement}s in the given {@link Diagram}.
    * @param diagram The {@link Diagram} to list contained {@link PictogramElement}s.
    * @return The contained {@link PictogramElement}s.
    */
   public static PictogramElement[] getAllPictogramElements(Diagram diagram) {
      List<PictogramElement> result = new LinkedList<PictogramElement>();
      if (diagram != null) {
         TreeIterator<EObject> iter = diagram.eAllContents();
         while (iter.hasNext()) {
            EObject next = iter.next();
            if (next instanceof PictogramElement) {
               result.add((PictogramElement)next);
            }
         }
      }
      return result.toArray(new PictogramElement[result.size()]);
   }
}
