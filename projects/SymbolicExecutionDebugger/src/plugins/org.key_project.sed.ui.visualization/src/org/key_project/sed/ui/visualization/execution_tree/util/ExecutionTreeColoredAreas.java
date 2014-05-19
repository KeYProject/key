package org.key_project.sed.ui.visualization.execution_tree.util;

import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.emf.common.util.EList;
import org.eclipse.graphiti.mm.algorithms.styles.AdaptedGradientColoredAreas;
import org.eclipse.graphiti.mm.algorithms.styles.GradientColoredArea;
import org.eclipse.graphiti.mm.algorithms.styles.GradientColoredAreas;
import org.eclipse.graphiti.mm.algorithms.styles.LocationType;
import org.eclipse.graphiti.mm.algorithms.styles.StylesFactory;
import org.eclipse.graphiti.util.IGradientType;
import org.eclipse.graphiti.util.IPredefinedRenderingStyle;
import org.eclipse.graphiti.util.PredefinedColoredAreas;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.util.VisualizationPreferences;

/**
 * Provides the gradient colored areas used for execution tree nodes.
 * @author Martin Hentschel
 */
public class ExecutionTreeColoredAreas extends PredefinedColoredAreas {
   /**
    * Creates the {@link AdaptedGradientColoredAreas} for an {@link ISEDDebugNode} with the given {@link ISEDAnnotation}s.
    * @param annotations The {@link ISEDAnnotation}s.
    * @return The created {@link AdaptedGradientColoredAreas}.
    */
   public static AdaptedGradientColoredAreas createExecutionTreeNodeAdaptions(ISEDAnnotation[] annotations) {
      AdaptedGradientColoredAreas agca = StylesFactory.eINSTANCE.createAdaptedGradientColoredAreas();
      agca.setGradientType(VisualizationPreferences.isExecutionTreeNodeDirectionHorizontal() ? IGradientType.HORIZONTAL : IGradientType.VERTICAL);
      
      List<ISEDAnnotation> backgroundAnnotations = new LinkedList<ISEDAnnotation>();
      for (ISEDAnnotation annotation : annotations) {
         if (annotation.isEnabled() && annotation.isHighlightBackground()) {
            backgroundAnnotations.add(annotation);
         }
      }
      
      List<RGB> normalColors = new LinkedList<RGB>();
      List<RGB> primaryColors = new LinkedList<RGB>();
      List<RGB> secondaryColors = new LinkedList<RGB>();
      if (backgroundAnnotations.isEmpty()) {
         RGB start = VisualizationPreferences.getExecutionTreeNodeFirstBackgroundColor();
         RGB end = VisualizationPreferences.getExecutionTreeNodeSecondBackgroundColor();
         normalColors.add(start);
         normalColors.add(end);
         primaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(start, 0.7f));
         primaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(end, 0.7f));
         secondaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(start, 0.85f));
         secondaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(end, 0.85f));
      }
      else if (backgroundAnnotations.size() == 1) {
         RGB start = backgroundAnnotations.get(0).getBackgroundColor();
         RGB end = VisualizationPreferences.getExecutionTreeNodeSecondBackgroundColor();
         normalColors.add(start);
         normalColors.add(end);
         primaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(start, 0.7f));
         primaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(end, 0.7f));
         secondaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(start, 0.85f));
         secondaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(end, 0.85f));
      }
      else {
         for (ISEDAnnotation annotation : backgroundAnnotations) {
            RGB rgb = annotation.getBackgroundColor();
            normalColors.add(rgb);
            primaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(rgb, 0.7f));
            secondaryColors.add(org.key_project.util.java.ColorUtil.scaleBrightness(rgb, 0.85f));
         }
      }
      // Create areas (without IPredefinedRenderingStyle.STYLE_ADAPTATION_ACTION_ALLOWED and IPredefinedRenderingStyle.STYLE_ADAPTATION_ACTION_FORBIDDEN)
      agca.getAdaptedGradientColoredAreas().add(IPredefinedRenderingStyle.STYLE_ADAPTATION_DEFAULT, createExecutionTreeNodeGradientColoredAreas(IPredefinedRenderingStyle.STYLE_ADAPTATION_DEFAULT, normalColors));
      agca.getAdaptedGradientColoredAreas().add(IPredefinedRenderingStyle.STYLE_ADAPTATION_PRIMARY_SELECTED, createExecutionTreeNodeGradientColoredAreas(IPredefinedRenderingStyle.STYLE_ADAPTATION_DEFAULT, primaryColors));
      agca.getAdaptedGradientColoredAreas().add(IPredefinedRenderingStyle.STYLE_ADAPTATION_SECONDARY_SELECTED, createExecutionTreeNodeGradientColoredAreas(IPredefinedRenderingStyle.STYLE_ADAPTATION_DEFAULT, secondaryColors));
      return agca;
   }
   
   /**
    * Creates a {@link GradientColoredAreas} for the given {@link RGB}s.
    * @param styleAdaption The style adaption.
    * @param colors The {@link RGB}s.
    * @return The created {@link GradientColoredAreas}.
    */
   protected static GradientColoredAreas createExecutionTreeNodeGradientColoredAreas(int styleAdaption, List<RGB> colors) {
      final GradientColoredAreas gradientColoredAreas = StylesFactory.eINSTANCE.createGradientColoredAreas();
      final EList<GradientColoredArea> gcas = gradientColoredAreas.getGradientColor();
      int width = 100 / (colors.size() - 1);
      int index = 0;
      Assert.isTrue(colors.size() >= 2);
      Iterator<RGB> iter = colors.iterator();
      RGB previous = iter.next();
      while (iter.hasNext()) {
         RGB current = iter.next();
         addGradientColoredArea(gcas, 
                                org.key_project.util.java.ColorUtil.toHexRGBString(previous), 
                                index, 
                                LocationType.LOCATION_TYPE_RELATIVE, 
                                org.key_project.util.java.ColorUtil.toHexRGBString(current), 
                                index += width, 
                                LocationType.LOCATION_TYPE_RELATIVE);
         previous = current;
      }
      gradientColoredAreas.setStyleAdaption(styleAdaption);
      return gradientColoredAreas;
   }
}
