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

package org.key_project.sed.ui.visualization.object_diagram.util;

import org.eclipse.graphiti.mm.algorithms.styles.Style;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.util.ColorConstant;
import org.eclipse.graphiti.util.IColorConstant;
import org.eclipse.graphiti.util.PredefinedColoredAreas;
import org.key_project.sed.ui.visualization.model.od.ODAssociation;
import org.key_project.sed.ui.visualization.model.od.ODObject;
import org.key_project.sed.ui.visualization.model.od.ODValue;
import org.key_project.sed.ui.visualization.util.GraphitiUtil;

/**
 * Provides the style used in object diagrams.
 * @author Martin Hentschel
 */
public final class ObjectDiagramStyleUtil {
   /**
    * The foreground color for text in {@link ODObject}s.
    */
   public static final IColorConstant OBJECT_FOREGROUND = new ColorConstant(67, 106, 149);
   
   /**
    * The foreground color for {@link ODObject}s.
    */
   public static final IColorConstant OBJECT_TEXT_FOREGROUND = IColorConstant.BLACK;
   
   /**
    * The foreground color for {@link ODValue}s.
    */
   public static final IColorConstant VALUE_TEXT_FOREGROUND = IColorConstant.BLACK;
   
   /**
    * The foreground color for {@link ODAssociation}s.
    */
   public static final IColorConstant ASSOCIATION_FOREGROUND = IColorConstant.BLACK;
   
   /**
    * The foreground color for text of {@link ODAssociation}s.
    */
   public static final IColorConstant ASSOCIATION_TEXT_FOREGROUND = IColorConstant.BLACK;

   /**
    * Forbid instances.
    */
   private ObjectDiagramStyleUtil() {
   }
   
   /**
    * Returns the {@link Style} used for {@link ODObject}s.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for {@link ODObject}s.
    */
   public static Style getStyleForObject(Diagram diagram) {
      final String STYLE_ID = "object";
      Style style = GraphitiUtil.findStyle(diagram, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(diagram, STYLE_ID);
         style.setForeground(gaService.manageColor(diagram, OBJECT_FOREGROUND));
         gaService.setRenderingStyle(style, PredefinedColoredAreas.getBlueWhiteGlossAdaptions());
         style.setLineWidth(2);
         style.setFont(GraphitiUtil.getDefaultFont(diagram));
      }
      return style;
   }

   /**
    * Returns the {@link Style} used for text in {@link ODObject}s.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for text in {@link ODObject}s.
    */
   public static Style getStyleForObjectText(Diagram diagram) {
      final String STYLE_ID = "objectText";
      // this is a child style of the e-class-style
      Style parentStyle = getStyleForObject(diagram);
      Style style = GraphitiUtil.findStyle(parentStyle, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(getStyleForObject(diagram), STYLE_ID);
         // "overwrites" values from parent style
         style.setForeground(gaService.manageColor(diagram, OBJECT_TEXT_FOREGROUND));
         style.setFont(GraphitiUtil.getDefaultFont(diagram));
      }
      return style;
   }

   /**
    * Returns the {@link Style} used for text in {@link ODValue}s.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for text in {@link ODValue}s.
    */
   public static Style getStyleForValueText(Diagram diagram) {
      final String STYLE_ID = "valueText";
      // this is a child style of the e-class-style
      Style parentStyle = getStyleForObject(diagram);
      Style style = GraphitiUtil.findStyle(parentStyle, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(getStyleForObject(diagram), STYLE_ID);
         // "overwrites" values from parent style
         style.setForeground(gaService.manageColor(diagram, VALUE_TEXT_FOREGROUND));
         style.setFont(GraphitiUtil.getDefaultFont(diagram));
      }
      return style;
   }

   /**
    * Returns the {@link Style} used for {@link ODAssociation}s.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for {@link ODAssociation}s.
    */
   public static Style getStyleForAssociation(Diagram diagram) {
      final String STYLE_ID = "association";
      // this is a child style of the e-class-style
      Style parentStyle = getStyleForObject(diagram);
      Style style = GraphitiUtil.findStyle(parentStyle, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(getStyleForObject(diagram), STYLE_ID);
         // "overwrites" values from parent style
         gaService.setRenderingStyle(style, PredefinedColoredAreas.getCopperWhiteGlossAdaptions());
         style.setForeground(gaService.manageColor(diagram, ASSOCIATION_FOREGROUND));
         style.setFont(GraphitiUtil.getDefaultFont(diagram));
      }
      return style;
   }

   /**
    * Returns the {@link Style} used for text in {@link ODAssociation}s.
    * @param diagram The {@link Diagram} to use the {@link Style} in.
    * @return The {@link Style} for text in {@link ODAssociation}s.
    */
   public static Style getStyleForAssociationText(Diagram diagram) {
      final String STYLE_ID = "associationText";
      // this is a child style of the e-class-style
      Style parentStyle = getStyleForObject(diagram);
      Style style = GraphitiUtil.findStyle(parentStyle, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(getStyleForObject(diagram), STYLE_ID);
         // "overwrites" values from parent style
         style.setForeground(gaService.manageColor(diagram, ASSOCIATION_TEXT_FOREGROUND));
         style.setFont(GraphitiUtil.getDefaultFont(diagram));
      }
      return style;
   }
}