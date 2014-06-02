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

package org.key_project.sed.ui.visualization.execution_tree.util;

import org.eclipse.graphiti.mm.algorithms.styles.AdaptedGradientColoredAreas;
import org.eclipse.graphiti.mm.algorithms.styles.Style;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.util.ColorConstant;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;
import org.key_project.sed.ui.visualization.util.VisualizationPreferences;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

/**
 * Provides the style used in execution trees.
 * @author Martin Hentschel
 */
public final class ExecutionTreeStyleUtil {
   /**
    * Forbid instances.
    */
   private ExecutionTreeStyleUtil() {
   }
   
   /**
    * Returns the {@link Style} used for {@link ISEDDebugNode}s.
    * @param annotations The available {@link ISEDAnnotation}.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for {@link ISEDDebugNode}s.
    */
   public static Style getStyleForDebugNode(ISEDAnnotation[] annotations, Diagram diagram) {
      String styleId = computeDebugNodeStyleId(annotations);
      return getStyleForDebugNode(styleId, annotations, diagram);
   }
   
   /**
    * Returns the {@link Style} used for {@link ISEDDebugNode}s.
    * @param styleId The style ID to use.
    * @param annotations The available {@link ISEDAnnotation}.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for {@link ISEDDebugNode}s.
    */
   public static Style getStyleForDebugNode(String styleId, ISEDAnnotation[] annotations, Diagram diagram) {
      Style style = GraphitiUtil.findStyle(diagram, styleId);
      IGaService gaService = Graphiti.getGaService();
      if (style == null) { // style not found - create new style
         style = gaService.createStyle(diagram, styleId);
         style.setLineWidth(2);
         style.setFont(GraphitiUtil.getDefaultFont(diagram));
      }
      ISEDAnnotation foregroundAnnotation = searchForegroundAnnotation(annotations);
      if (foregroundAnnotation != null) {
         RGB rgb = foregroundAnnotation.getForegroundColor();
         style.setForeground(gaService.manageColor(diagram, new ColorConstant(rgb.red, rgb.green, rgb.blue)));
      }
      else {
         RGB rgb = VisualizationPreferences.getExecutionTreeNodeForegroundColor();
         style.setForeground(gaService.manageColor(diagram, new ColorConstant(rgb.red, rgb.green, rgb.blue)));
      }
      AdaptedGradientColoredAreas areas = ExecutionTreeColoredAreas.createExecutionTreeNodeAdaptions(annotations);
      gaService.setRenderingStyle(style, areas);
      return style;
   }

   /**
    * Returns the {@link Style} used for text in {@link ISEDDebugNode}s.
    * @param annotations The available {@link ISEDAnnotation}.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for text in {@link ISEDDebugNode}s.
    */
   public static Style getStyleForDebugNodeText(ISEDAnnotation[] annotations, Diagram diagram) {
      String styleId = computeDebugNodeTextStyleId(annotations);
      return getStyleForDebugNodeText(styleId, annotations, diagram);
   }

   /**
    * Returns the {@link Style} used for text in {@link ISEDDebugNode}s.
    * @param styleId The style ID to use.
    * @param annotations The available {@link ISEDAnnotation}.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for text in {@link ISEDDebugNode}s.
    */
   public static Style getStyleForDebugNodeText(String styleId, ISEDAnnotation[] annotations, Diagram diagram) {
      Style style = GraphitiUtil.findStyle(diagram, styleId);
      IGaService gaService = Graphiti.getGaService();
      if (style == null) { // style not found - create new style
         style = gaService.createStyle(diagram, styleId);
         style.setLineWidth(2);
         style.setFont(GraphitiUtil.getDefaultFont(diagram));
      }
      ISEDAnnotation foregroundAnnotation = searchForegroundAnnotation(annotations);
      if (foregroundAnnotation != null) {
         RGB rgb = foregroundAnnotation.getForegroundColor();
         style.setForeground(gaService.manageColor(diagram, new ColorConstant(rgb.red, rgb.green, rgb.blue)));
      }
      else {
         RGB rgb = VisualizationPreferences.getExecutionTreeNodeTextColor();
         style.setForeground(gaService.manageColor(diagram, new ColorConstant(rgb.red, rgb.green, rgb.blue)));
      }
      return style;
   }
   
   /**
    * Searches the first {@link ISEDAnnotation} which is enabled and defines a foreground color.
    * @param annotations The {@link ISEDAnnotation}s to search in.
    * @return The found {@link ISEDAnnotation} or {@code null} if not available.
    */
   public static ISEDAnnotation searchForegroundAnnotation(ISEDAnnotation[] annotations) {
      return ArrayUtil.search(annotations, new IFilter<ISEDAnnotation>() {
         @Override
         public boolean select(ISEDAnnotation element) {
            return element.isEnabled() && element.isHighlightForeground();
         }
      });
   }

   /**
    * Computes the style ID for texts of debug nodes.
    * @param annotations The {@link ISEDAnnotation}s.
    * @return The style ID.
    */
   public static String computeDebugNodeTextStyleId(ISEDAnnotation[] annotations) {
      return computeStyleId("debugNodeText", annotations);
   }

   /**
    * Computes the style ID for debug nodes.
    * @param annotations The {@link ISEDAnnotation}s.
    * @return The style ID.
    */
   public static String computeDebugNodeStyleId(ISEDAnnotation[] annotations) {
      return computeStyleId("debugNode", annotations);
   }

   /**
    * Computes a style ID.
    * @param prefix The prefix.
    * @param annotations The {@link ISEDAnnotation}s.
    * @return The computed style ID.
    */
   public static String computeStyleId(String prefix, ISEDAnnotation[] annotations) {
      if (!ArrayUtil.isEmpty(annotations)) {
         StringBuffer sb = new StringBuffer();
         for (ISEDAnnotation annotation : annotations) {
            sb.append("_");
            sb.append(annotation.getId());
         }
         sb.append(prefix);
         return sb.toString();
      }
      else {
         return prefix;
      }
   }

   /**
    * Returns the {@link Style} used for text in {@link ISEDDebugNode}s.
    * @param node The {@link ISEDDebugNode} for which the {@link Style} will be used.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for text in {@link ISEDDebugNode}s.
    */
   public static Style getStyleForParentConnection(Diagram diagram) {
      final String STYLE_ID = "parentConnection";
      Style style = GraphitiUtil.findStyle(diagram, STYLE_ID);
      IGaService gaService = Graphiti.getGaService();
      if (style == null) { // style not found - create new style
         style = gaService.createStyle(diagram, STYLE_ID);
         style.setLineWidth(2);
         style.setFont(GraphitiUtil.getDefaultFont(diagram));
      }
      RGB rgb = VisualizationPreferences.getExecutionTreeNodeConnectionColor();
      style.setForeground(gaService.manageColor(diagram, new ColorConstant(rgb.red, rgb.green, rgb.blue)));
      return style;
   }
}