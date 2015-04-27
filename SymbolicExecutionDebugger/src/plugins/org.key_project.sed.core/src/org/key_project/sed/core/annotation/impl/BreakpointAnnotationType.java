package org.key_project.sed.core.annotation.impl;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

/**
 * The {@link ISEDAnnotationType} used for breakpoints.
 * @author Martin Hentschel
 * @see BreakpointAnnotation
 * @see BreakpointAnnotationLink
 */
public class BreakpointAnnotationType extends AbstractSEDAnnotationType {
   /**
    * The ID of this annotation type.
    */
   public static final String TYPE_ID = "org.key_project.sed.core.annotationType.breakpoint";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getTypeId() {
      return TYPE_ID;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String getName() {
      return "Breakpoints";
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDefaultHighlightBackground() {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getDefaultBackgroundColor() {
      return new RGB(163, 73, 164); // pink
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDefaultHighlightForeground() {
      return false;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public RGB getDefaultForegroundColor() {
      return new RGB(0, 0, 0); // black
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public BreakpointAnnotation createAnnotation() {
      return new BreakpointAnnotation();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public BreakpointAnnotationLink createLink(ISEDAnnotation source, ISEDDebugNode target) {
      return new BreakpointAnnotationLink(source, target);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getAdditionalLinkColumns(ISEDAnnotation annotation) {
      return new String[] {"Breakpoint"};
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getAdditionalLinkColumnValue(int index, ISEDAnnotationLink link) {
      if (link instanceof BreakpointAnnotationLink) {
         if (index == 0) {
            return ((BreakpointAnnotationLink) link).getBreakpointName();
         }
         else {
            return null;
         }
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotation(ISEDAnnotation annotation) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotation(ISEDAnnotation annotation, String savedContent) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotationLink(ISEDAnnotationLink link) {
      Assert.isTrue(link instanceof BreakpointAnnotationLink);
      return ((BreakpointAnnotationLink)link).getBreakpointName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotationLink(ISEDAnnotationLink link, String savedContent) {
      Assert.isTrue(link instanceof BreakpointAnnotationLink);
      ((BreakpointAnnotationLink)link).setBreakpointName(savedContent);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeNode(ISEDDebugNode node, ISEDAnnotation annotation) throws DebugException {
      if (node != null && annotation instanceof BreakpointAnnotation) {
         IBreakpoint[] breakpoints = node.computeHitBreakpoints();
         if (breakpoints != null) {
            for (IBreakpoint breakpoint : breakpoints) {
               addBreakpointLink(node, annotation, breakpoint);
            }
         }
      }
   }
   
   /**
    * Adds a {@link BreakpointAnnotationLink} to the {@link ISEDDebugNode}.
    * @param node The {@link ISEDDebugNode} to add link to.
    * @param annotation The source {@link ISEDAnnotation}.
    * @param breakpoint The {@link IBreakpoint} represented by the added {@link BreakpointAnnotationLink}.
    */
   public void addBreakpointLink(ISEDDebugNode node, ISEDAnnotation annotation, IBreakpoint breakpoint) {
      BreakpointAnnotationLink link = (BreakpointAnnotationLink)annotation.getType().createLink(annotation, node);
      link.setBreakpoint(breakpoint);
      node.addAnnotationLink(link);
   }

   /**
    * Checks if the given {@link ISEDDebugNode} has at least one link representing the given {@link IBreakpoint}.
    * @param node The {@link ISEDDebugNode} to check.
    * @param breakpoint The {@link IBreakpoint} to check.
    * @return {@code true} at least one link is available, {@code false} if no link is available.
    */
   public boolean hasLink(ISEDDebugNode node, 
                          final IBreakpoint breakpoint) {
      ISEDAnnotationLink[] links = node.getAnnotationLinks(this);
      return ArrayUtil.search(links, new IFilter<ISEDAnnotationLink>() {
         @Override
         public boolean select(ISEDAnnotationLink element) {
            return isBreakpointLink(element, breakpoint);
         }
      }) != null;
   }
   
   /**
    * Checks if the given {@link ISEDAnnotationLink} represents the given {@link IBreakpoint}.
    * @param link The {@link ISEDAnnotationLink} to check.
    * @param breakpoint The {@link IBreakpoint} to check.
    * @return {@code true} link represents breakpoint, {@code false} otherwise.
    */
   public boolean isBreakpointLink(ISEDAnnotationLink link, IBreakpoint breakpoint) {
      return link instanceof BreakpointAnnotationLink &&
             ((BreakpointAnnotationLink)link).getBreakpoint() == breakpoint;
   }
}
