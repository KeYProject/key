package org.key_project.sed.ui.visualization.util;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Path;
import org.eclipse.draw2d.TextUtilities;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.transaction.RecordingCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.datatypes.IDimension;
import org.eclipse.graphiti.internal.datatypes.impl.DimensionImpl;
import org.eclipse.graphiti.mm.algorithms.styles.Font;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.ui.editor.DiagramEditorFactory;
import org.eclipse.graphiti.ui.editor.DiagramEditorInput;
import org.eclipse.graphiti.ui.internal.services.impl.GefService;
import org.eclipse.graphiti.ui.internal.util.DataTypeTransformation;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.eclipse.graphiti.ui.services.IUiLayoutService;
import org.eclipse.swt.widgets.Display;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

/**
 * Provides static utility methods for Graphiti.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class GraphitiUtil {
   /**
    * Forbid instances.
    */
   private GraphitiUtil() {
   }
   
   /**
    * Calculates the string size of the given text in the given {@link Font}.
    * Line breaks and tabs are ignored and treated as normal space.
    * @param text The text.
    * @param font The {@link Font}.
    * @return The calculated text size.
    */
   public static IDimension calculateStringSize(final String text, final Font font) {
      IRunnableWithResult<IDimension> run = new AbstractRunnableWithResult<IDimension>() {
         @Override
         public void run() {
            setResult(GraphitiUi.getUiLayoutService().calculateTextSize(text, font));
         }
      };
      Display.getDefault().syncExec(run);
      return run.getResult();
   }
   
   /**
    * <p>
    * Calculates the text size of the given text in the given {@link Font}.
    * Linebreaks and tabs are treated as real line break/tab.
    * </p>
    * <p>
    * The implementation is a modified copy of {@link GefService#calculateTextSize(String, Font)}
    * which is the internal implementation of {@link IUiLayoutService#calculateTextSize(String, Font)}.
    * But the provided Graphiti implementation calculates the string size and not the text size.
    * </p>
    * @param text The text.
    * @param font The {@link Font}.
    * @return The calculated text size.
    */
   public static IDimension calculateTextSize(final String text, final Font font) {
      if (text == null || font == null || font.getName() == null) {
         return null;
      }
      else {
         IRunnableWithResult<IDimension> run = new AbstractRunnableWithResult<IDimension>() {
            @Override
            public void run() {
               org.eclipse.swt.graphics.Font swtFont = DataTypeTransformation.toSwtFont(font);
               if (swtFont != null) {
                  Dimension se = TextUtilities.INSTANCE.getTextExtents(text, swtFont);
                  if (se != null) {
                     IDimension dimension = new DimensionImpl(se.width, se.height);
                     setResult(dimension);
                  }
                  if (!swtFont.isDisposed()) {
                     swtFont.dispose();
                  }
               }
            }
         };
         Display.getDefault().syncExec(run);
         return run.getResult();
      }
   }
   
   /**
    * Creates a {@link TransactionalEditingDomain} and a {@link Resource}
    * for the given {@link URI} which contains the given {@link Diagram} as only content.
    * @param diagram The {@link Diagram} to add to a new {@link Resource}.
    * @param uri The {@link URI} of the new {@link Resource}.
    * @return The used {@link TransactionalEditingDomain}.
    */
   public static TransactionalEditingDomain createDomainAndResource(final Diagram diagram, URI uri) {
      if (uri == null) {
         throw new IllegalArgumentException("The URI is null.");
      }
      if (diagram != null && diagram.eResource() != null) {
         throw new IllegalArgumentException("The Diagram is already contained in a Resource.");
      }
      TransactionalEditingDomain domain = DiagramEditorFactory.createResourceSetAndEditingDomain();
      final Resource resource = domain.getResourceSet().createResource(uri);
      if (diagram != null) {
         domain.getCommandStack().execute(new RecordingCommand(domain) {
            @Override
            protected void doExecute() {
               resource.getContents().add(diagram);
            }

            @Override
            public boolean canUndo() {
               return false;
            }
         });
      }
      return domain;
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
