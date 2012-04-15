package org.key_project.sed.ui.visualization.execution_tree.util;

import java.util.Collection;

import org.eclipse.graphiti.mm.StyleContainer;
import org.eclipse.graphiti.mm.algorithms.styles.Style;
import org.eclipse.graphiti.mm.pictograms.Diagram;
import org.eclipse.graphiti.services.Graphiti;
import org.eclipse.graphiti.services.IGaService;
import org.eclipse.graphiti.util.ColorConstant;
import org.eclipse.graphiti.util.IColorConstant;
import org.eclipse.graphiti.util.PredefinedColoredAreas;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.util.java.ObjectUtil;

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
      Style style = findStyle(diagram, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(diagram, STYLE_ID);
         style.setForeground(gaService.manageColor(diagram, DEBUG_NODE_FOREGROUND));
         gaService.setRenderingStyle(style, PredefinedColoredAreas.getBlueWhiteGlossAdaptions());
         style.setLineWidth(2);
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
      Style style = findStyle(parentStyle, STYLE_ID);
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
      Style style = findStyle(parentStyle, STYLE_ID);
      if (style == null) { // style not found - create new style
         IGaService gaService = Graphiti.getGaService();
         style = gaService.createStyle(getStyleForDebugNode(diagram), STYLE_ID);
         // "overwrites" values from parent style
         style.setForeground(gaService.manageColor(diagram, PARENT_CONNECTION_FOREGROUND));
      }
      return style;
   }

   /**
    * Searches a style with the given ID in the given {@link StyleContainer}.
    * @param styleContainer The {@link StyleContainer} to search in.
    * @param id The ID of the style to search.
    * @return The found {@link Style} or {@code null} if no style with the given ID is available.
    */
   protected static Style findStyle(StyleContainer styleContainer, String id) {
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
}