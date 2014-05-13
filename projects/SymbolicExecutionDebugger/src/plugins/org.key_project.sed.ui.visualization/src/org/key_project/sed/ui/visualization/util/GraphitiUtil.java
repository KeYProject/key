/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.ui.visualization.util;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.Path;
import org.eclipse.draw2d.PositionConstants;
import org.eclipse.draw2d.TextUtilities;
import org.eclipse.draw2d.geometry.Dimension;
import org.eclipse.draw2d.geometry.Insets;
import org.eclipse.draw2d.graph.CompoundDirectedGraph;
import org.eclipse.draw2d.graph.CompoundDirectedGraphLayout;
import org.eclipse.draw2d.graph.Edge;
import org.eclipse.draw2d.graph.EdgeList;
import org.eclipse.draw2d.graph.Node;
import org.eclipse.draw2d.graph.NodeList;
import org.eclipse.emf.common.util.TreeIterator;
import org.eclipse.emf.common.util.URI;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.emf.ecore.resource.Resource;
import org.eclipse.emf.transaction.RecordingCommand;
import org.eclipse.emf.transaction.TransactionalEditingDomain;
import org.eclipse.graphiti.datatypes.IDimension;
import org.eclipse.graphiti.datatypes.ILocation;
import org.eclipse.graphiti.dt.IDiagramTypeProvider;
import org.eclipse.graphiti.features.IFeatureProvider;
import org.eclipse.graphiti.features.context.IContext;
import org.eclipse.graphiti.features.context.impl.LayoutContext;
import org.eclipse.graphiti.internal.datatypes.impl.DimensionImpl;
import org.eclipse.graphiti.internal.datatypes.impl.LocationImpl;
import org.eclipse.graphiti.internal.services.impl.GaServiceImpl;
import org.eclipse.graphiti.mm.StyleContainer;
import org.eclipse.graphiti.mm.algorithms.GraphicsAlgorithm;
import org.eclipse.graphiti.mm.algorithms.styles.Font;
import org.eclipse.graphiti.mm.algorithms.styles.Style;
import org.eclipse.graphiti.mm.pictograms.Anchor;
import org.eclipse.graphiti.mm.pictograms.AnchorContainer;
import org.eclipse.graphiti.mm.pictograms.Connection;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.mm.pictograms.PictogramElement;
import org.eclipse.graphiti.mm.pictograms.Shape;
import org.eclipse.graphiti.platform.IDiagramEditor;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.ui.editor.DiagramEditorFactory;
import org.eclipse.graphiti.ui.editor.DiagramEditorInput;
import org.eclipse.graphiti.ui.internal.services.impl.GefService;
import org.eclipse.graphiti.ui.internal.util.DataTypeTransformation;
import org.eclipse.graphiti.ui.services.GraphitiUi;
import org.eclipse.graphiti.ui.services.IUiLayoutService;
import org.eclipse.swt.widgets.Display;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;

/**
 * Provides static utility methods for Graphiti.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public final class GraphitiUtil {
   /**
    * Property which is used in {@link IContext} instances to define
    * an {@link IProgressMonitor} used during feature execution. It is
    * accessible via {@link IContext#getProperty(Object)}.
    */
   public static final String CONTEXT_PROPERTY_MONITOR = "org.key_project.sed.ui.visualization.feature.property.monitor";
   
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

   /**
    * Searches a style with the given ID in the given {@link StyleContainer}.
    * @param styleContainer The {@link StyleContainer} to search in.
    * @param id The ID of the style to search.
    * @return The found {@link Style} or {@code null} if no style with the given ID is available.
    */
   public static Style findStyle(StyleContainer styleContainer, String id) {
      Collection<Style> styles = styleContainer.getStyles();
      if (styles != null) {
         for (Style style : styles) {
            if (ObjectUtil.equals(id, style.getId())) {
               return style;
            }
         }
      }
      return null;
   }
   
   /**
    * Returns the default font of the given {@link Diagram}.
    * @param diagram The {@link Diagram} to get its default font.
    * @return The default font or {@code null} if the given {@link Diagram} is {@code null}.
    */
   public static Font getDefaultFont(Diagram diagram) {
      if (diagram != null) {
         IGaService gaService = Graphiti.getGaService();
         return gaService.manageFont(diagram, GaServiceImpl.DEFAULT_FONT, 10);
      }
      else {
         return null;
      }
   }

   /**
    * <p>
    * Layouts the nodes and connections directly contained at top level 
    * in the given {@link Diagram}.
    * </p>
    * <p>
    * The code was copied from the Snippet of Graphiti's FAQ page:
    * <a href="http://www.eclipse.org/graphiti/developers/resources/TutorialLayoutDiagramFeature.java">http://www.eclipse.org/graphiti/developers/resources/TutorialLayoutDiagramFeature.java</a>
    * </p>
    * @param fp The {@link IFeatureProvider} to use to layout resized elements.
    * @param diagram The {@link Diagram} to layout.
    * @param padding The padding to use, default is {@code 30}.
    * @param eastDirectionInsteadOfSouth Layout to the east instead of south.
    * @param allowResizing Allow resizing of elements?
    * @param monitor The {@link IProgressMonitor} to use.
    */
   public static void layoutTopLevelElements(IFeatureProvider fp,
                                             Diagram diagram, 
                                             int padding, 
                                             boolean eastDirectionInsteadOfSouth,
                                             boolean allowResizing,
                                             IProgressMonitor monitor) {
      if (diagram != null) {
         CompoundDirectedGraph graph = mapDiagramToGraph(diagram, monitor);
         monitor.setTaskName("Executing GEF layouter.");
         graph.setDefaultPadding(new Insets(padding));
         graph.setDirection(eastDirectionInsteadOfSouth ? PositionConstants.EAST : PositionConstants.SOUTH);
         new CompoundDirectedGraphLayout().visit(graph);
         monitor.worked(1);
         mapGraphCoordinatesToDiagram(fp, graph, allowResizing, monitor);
         monitor.done();
      }
   }

   /**
    * <p>
    * Utility method for {@link #layout(Diagram, int)} which maps the
    * elements and connections of Graphiti's {@link Diagram} into
    * a {@link CompoundDirectedGraph} of GEF.
    * </p>
    * <p>
    * The code was copied from the Snippet of Graphiti's FAQ page:
    * <a href="http://www.eclipse.org/graphiti/developers/resources/TutorialLayoutDiagramFeature.java">http://www.eclipse.org/graphiti/developers/resources/TutorialLayoutDiagramFeature.java</a>
    * </p>
    * @param diagram The {@link Diagram} to convert.
    * @param monitor The {@link IProgressMonitor} to use.
    * @return The result of the conversion.
    */
   @SuppressWarnings("unchecked")
   private static CompoundDirectedGraph mapDiagramToGraph(Diagram diagram, 
                                                          IProgressMonitor monitor) {
      Map<AnchorContainer, Node> shapeToNode = new HashMap<AnchorContainer, Node>();
      CompoundDirectedGraph dg = new CompoundDirectedGraph();
      EdgeList edgeList = new EdgeList();
      NodeList nodeList = new NodeList();
      monitor.beginTask("Layouting diagram", edgeList.size() * 2 + nodeList.size() * 2 + 1);
      monitor.setTaskName("Generating model for GEF layouter.");
      List<Shape> children = diagram.getChildren();
      for (Shape shape : children) {
         Node node = new Node();
         GraphicsAlgorithm ga = shape.getGraphicsAlgorithm();
         node.x = ga.getX();
         node.y = ga.getY();
         node.width = ga.getWidth();
         node.height = ga.getHeight();
         node.data = shape;
         shapeToNode.put(shape, node);
         nodeList.add(node);
         monitor.worked(1);
      }
      List<Connection> connections = diagram.getConnections();
      for (Connection connection : connections) {
         AnchorContainer source = connection.getStart().getParent();
         AnchorContainer target = connection.getEnd().getParent();
         Edge edge = new Edge(shapeToNode.get(source), shapeToNode.get(target));
         edge.data = connection;
         edgeList.add(edge);
         monitor.worked(1);
      }
      dg.nodes = nodeList;
      dg.edges = edgeList;
      return dg;
   }
   
   /**
    * <p>
    * Utility method for {@link #layout(Diagram, int)} which writes the
    * coordinates of the given GEF {@link CompoundDirectedGraph}
    * back to the elements and connections of Graphiti's {@link Diagram}.
    * </p>
    * <p>
    * The code was copied from the Snippet of Graphiti's FAQ page:
    * <a href="http://www.eclipse.org/graphiti/developers/resources/TutorialLayoutDiagramFeature.java">http://www.eclipse.org/graphiti/developers/resources/TutorialLayoutDiagramFeature.java</a>
    * </p>
    * @param fp The {@link IFeatureProvider} to use to layout resized elements.
    * @param graph The {@link CompoundDirectedGraph} which provides the new location and sizes
    * @param allowResizing Allow resizing of elements?
    * @param monitor The {@link IProgressMonitor} to use.
    */
   @SuppressWarnings("unchecked")
   private static void mapGraphCoordinatesToDiagram(IFeatureProvider fp,
                                                    CompoundDirectedGraph graph, 
                                                    boolean allowResizing,
                                                    IProgressMonitor monitor) {
      monitor.setTaskName("Updating diagram with data from GEF layouter.");
      NodeList myNodes = new NodeList();
      myNodes.addAll(graph.nodes);
      myNodes.addAll(graph.subgraphs);
      for (Object object : myNodes) {
         Node node = (Node) object;
         Shape shape = (Shape) node.data;
         if (allowResizing) {
            shape.getGraphicsAlgorithm().setX(node.x);
            shape.getGraphicsAlgorithm().setY(node.y);
            shape.getGraphicsAlgorithm().setWidth(node.width);
            shape.getGraphicsAlgorithm().setHeight(node.height);
            if (fp != null) {
               fp.layoutIfPossible(new LayoutContext(shape));
            }
         }
         else {
            // Center element in suggested size
            ILocation centered = center(new LocationImpl(node.x, node.y), 
                                        shape.getGraphicsAlgorithm(), 
                                        new LocationImpl(node.x + node.width, node.y + node.height));
            shape.getGraphicsAlgorithm().setX(centered.getX());
            shape.getGraphicsAlgorithm().setY(centered.getY());
         }
         monitor.worked(1);
      }
   }
   
   /**
    * Returns the center location of the given {@link Anchor}'s parent.
    * @param anchor The {@link Anchor} for which the center location is requested.
    * @return The center location of {@link Anchor}'s parent or {@code null} if not available.
    */
   public static ILocation getCenterLocation(Anchor anchor) {
      ILocation centerLocation = null;
      ILocation location = getLeftLocation(anchor);
      if (location != null) {
         IDimension dimension = getDimension(anchor);
         if (dimension != null) {
            centerLocation = new LocationImpl(location.getX() + dimension.getWidth() / 2,
                                              location.getY() + dimension.getHeight() / 2);
         }
      }
      return centerLocation;
   }
   
   /**
    * Returns the location of the given {@link Anchor}'s parent
    * which is the top left corner.
    * @param anchor The {@link Anchor} for which the location is requested.
    * @return The location of {@link Anchor}'s parent or {@code null} if not available.
    */
   public static ILocation getLeftLocation(Anchor anchor) {
      ILocation result = null;
      if (anchor != null && anchor.getParent() != null) {
         GraphicsAlgorithm ga = anchor.getParent().getGraphicsAlgorithm();
         if (ga != null) {
            result = new LocationImpl(ga.getX(), ga.getY());
         }
      }
      return result;
   }
   
   /**
    * Returns the location of the given {@link Anchor}'s parent
    * which is the bottom right corner.
    * @param anchor The {@link Anchor} for which the location is requested.
    * @return The location of {@link Anchor}'s parent or {@code null} if not available.
    */
   public static ILocation getRightLocation(Anchor anchor) {
      ILocation result = null;
      if (anchor != null && anchor.getParent() != null) {
         GraphicsAlgorithm ga = anchor.getParent().getGraphicsAlgorithm();
         if (ga != null) {
            result = new LocationImpl(ga.getX() + ga.getWidth(), ga.getY() + ga.getHeight());
         }
      }
      return result;
   }
   
   /**
    * Returns the dimension of the given {@link Anchor}'s parent.
    * @param anchor The {@link Anchor} for which the dimension is requested.
    * @return The dimension of {@link Anchor}'s parent or {@code null} if not available.
    */
   public static IDimension getDimension(Anchor anchor) {
      IDimension result = null;
      if (anchor != null && anchor.getParent() != null) {
         GraphicsAlgorithm ga = anchor.getParent().getGraphicsAlgorithm();
         if (ga != null) {
            result = new DimensionImpl(ga.getWidth(), ga.getHeight());
         }
      }
      return result;
   }

   /**
    * Computes an {@link ILocation} for the given {@link GraphicsAlgorithm}
    * which centers it exactly between the given start and end {@link ILocation}.
    * @param startLocation The start {@link ILocation}.
    * @param ga The {@link GraphicsAlgorithm} to center between start and end {@link ILocation}.
    * @param endLocation The end {@link ILocation}.
    * @return The {@link ILocation} which centers the given {@link GraphicsAlgorithm} between start and end {@link ILocation} or {@code null} if not available.
    */
   public static ILocation center(ILocation startLocation, GraphicsAlgorithm ga, ILocation endLocation) {
      ILocation result = null;
      if (startLocation != null && ga != null && endLocation != null) {
         result = new LocationImpl(((startLocation.getX() + endLocation.getX()) / 2) - (ga.getWidth() / 2),
                                   ((startLocation.getY() + endLocation.getY()) / 2) - (ga.getHeight() / 2));
      }
      return result;
   }

   /**
    * Computes an {@link ILocation} which is the center of the two given {@link ILocation}s.
    * @param startLocation The start {@link ILocation}.
    * @param endLocation The end {@link ILocation}.
    * @return The centered {@link ILocation} or {@code null} if one of the given {@link ILocation} is {@code null};
    */
   public static ILocation center(ILocation startLocation, ILocation endLocation) {
      if (startLocation != null && endLocation != null) {
         return new LocationImpl((startLocation.getX() + endLocation.getX()) / 2, 
                                 (startLocation.getY() + endLocation.getY()) / 2);
      }
      else {
         return null;
      }
   }

   /**
    * Selects the given {@link PictogramElement} in the editor if available.
    * @param featureProvider The {@link IFeatureProvider} used to find the editor.
    * @param pe The {@link PictogramElement} to select.
    */
   public static void select(IFeatureProvider featureProvider, PictogramElement pe) {
      if (featureProvider != null) {
         IDiagramTypeProvider typeProvider = featureProvider.getDiagramTypeProvider(); 
         if (typeProvider != null) {
            IDiagramEditor editor = typeProvider.getDiagramEditor();
            if (editor != null) {
               editor.setPictogramElementForSelection(pe);
            }
         }
      }
   }
   
   /**
    * Returns the {@link IProgressMonitor} defined in the given {@link IContext}.
    * If the given {@link IContext} is {@code null} or if it contains no one
    * a new {@link NullProgressMonitor} instance is returned.
    * @param context The {@link IContext}.
    * @return The defined {@link IProgressMonitor}.
    */
   public static IProgressMonitor getProgressMonitor(IContext context) {
      if (context != null) {
         Object contextMonitor = context.getProperty(CONTEXT_PROPERTY_MONITOR);
         if (contextMonitor instanceof IProgressMonitor) {
            return (IProgressMonitor)contextMonitor;
         }
         else {
            return new NullProgressMonitor();
         }
      }
      else {
         return new NullProgressMonitor();
      }
   }
}