/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
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

import org.eclipse.graphiti.mm.algorithms.styles.Style;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.util.ColorConstant;
import org.eclipse.graphiti.util.IColorConstant;
import org.eclipse.graphiti.util.PredefinedColoredAreas;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;

/**
 * Provides the style used in execution trees.
 * @author Martin Hentschel
 */
public final class ExecutionTreeStyleUtil {
   /**
    * The foreground color for text in {@link ISEDDebugNode}s.
    */
   public static final IColorConstant DEBUG_NODE_FOREGROUND = new ColorConstant(67, 106, 149);
   
   /**
    * The foreground color for {@link ISEDDebugNode}s.
    */
   public static final IColorConstant DEBUG_NODE_TEXT_FOREGROUND = IColorConstant.BLACK;
   
   /**
    * The foreground color for parent connection between {@link ISEDDebugNode}s.
    */
   public static final IColorConstant PARENT_CONNECTION_FOREGROUND = IColorConstant.BLACK;

   /**
    * Forbid instances.
    */
   private ExecutionTreeStyleUtil() {
   }
   
   /**
    * Returns the {@link Style} used for {@link ISEDDebugNode}s.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for {@link ISEDDebugNode}s.
    */
   public static Style getStyleForDebugNode(Diagram diagram) {
      final String STYLE_ID = "debugNode";
      Style style = GraphitiUtil.findStyle(diagram, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(diagram, STYLE_ID);
         style.setForeground(gaService.manageColor(diagram, DEBUG_NODE_FOREGROUND));
         gaService.setRenderingStyle(style, PredefinedColoredAreas.getBlueWhiteGlossAdaptions());
         style.setLineWidth(2);
         style.setFont(GraphitiUtil.getDefaultFont(diagram));
      }
      return style;
   }

   /**
    * Returns the {@link Style} used for text in {@link ISEDDebugNode}s.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for text in {@link ISEDDebugNode}s.
    */
   public static Style getStyleForDebugNodeText(Diagram diagram) {
      final String STYLE_ID = "debugNodeText";
      // this is a child style of the e-class-style
      Style parentStyle = getStyleForDebugNode(diagram);
      Style style = GraphitiUtil.findStyle(parentStyle, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(getStyleForDebugNode(diagram), STYLE_ID);
         // "overwrites" values from parent style
         style.setForeground(gaService.manageColor(diagram, DEBUG_NODE_TEXT_FOREGROUND));
      }
      return style;
   }

   /**
    * Returns the {@link Style} used for text in {@link ISEDDebugNode}s.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for text in {@link ISEDDebugNode}s.
    */
   public static Style getStyleForParentConnection(Diagram diagram) {
      final String STYLE_ID = "parentConnection";
      // this is a child style of the e-class-style
      Style parentStyle = getStyleForDebugNode(diagram);
      Style style = GraphitiUtil.findStyle(parentStyle, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(getStyleForDebugNode(diagram), STYLE_ID);
         // "overwrites" values from parent style
         style.setForeground(gaService.manageColor(diagram, PARENT_CONNECTION_FOREGROUND));
      }
      return style;
   }
}