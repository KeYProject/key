package org.key_project.sed.core.annotation.impl;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IBreakpoint;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEAnnotation;
import org.key_project.sed.core.annotation.ISEAnnotationLink;
import org.key_project.sed.core.annotation.ISEAnnotationType;
import org.key_project.sed.core.model.ISENode;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IFilter;

/**
 * The {@link ISEAnnotationType} used for breakpoints.
 * @author Martin Hentschel
 * @see BreakpointAnnotation
 * @see BreakpointAnnotationLink
 */
public class BreakpointAnnotationType extends AbstractSEAnnotationType {
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
   public BreakpointAnnotationLink createLink(ISEAnnotation source, ISENode target) {
      return new BreakpointAnnotationLink(source, target);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String[] getAdditionalLinkColumns(ISEAnnotation annotation) {
      return new String[] {"Breakpoint"};
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getAdditionalLinkColumnValue(int index, ISEAnnotationLink link) {
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
   public String saveAnnotation(ISEAnnotation annotation) {
      return null;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotation(ISEAnnotation annotation, String savedContent) {
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotationLink(ISEAnnotationLink link) {
      Assert.isTrue(link instanceof BreakpointAnnotationLink);
      return ((BreakpointAnnotationLink)link).getBreakpointName();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotationLink(ISEAnnotationLink link, String savedContent) {
      Assert.isTrue(link instanceof BreakpointAnnotationLink);
      ((BreakpointAnnotationLink)link).setBreakpointName(savedContent);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeNode(ISENode node, ISEAnnotation annotation) throws DebugException {
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
    * Adds a {@link BreakpointAnnotationLink} to the {@link ISENode}.
    * @param node The {@link ISENode} to add link to.
    * @param annotation The source {@link ISEAnnotation}.
    * @param breakpoint The {@link IBreakpoint} represented by the added {@link BreakpointAnnotationLink}.
    */
   public void addBreakpointLink(ISENode node, ISEAnnotation annotation, IBreakpoint breakpoint) {
      BreakpointAnnotationLink link = (BreakpointAnnotationLink)annotation.getType().createLink(annotation, node);
      link.setBreakpoint(breakpoint);
      node.addAnnotationLink(link);
   }

   /**
    * Checks if the given {@link ISENode} has at least one link representing the given {@link IBreakpoint}.
    * @param node The {@link ISENode} to check.
    * @param breakpoint The {@link IBreakpoint} to check.
    * @return {@code true} at least one link is available, {@code false} if no link is available.
    */
   public boolean hasLink(ISENode node, 
                          final IBreakpoint breakpoint) {
      ISEAnnotationLink[] links = node.getAnnotationLinks(this);
      return ArrayUtil.search(links, new IFilter<ISEAnnotationLink>() {
         @Override
         public boolean select(ISEAnnotationLink element) {
            return isBreakpointLink(element, breakpoint);
         }
      }) != null;
   }
   
   /**
    * Checks if the given {@link ISEAnnotationLink} represents the given {@link IBreakpoint}.
    * @param link The {@link ISEAnnotationLink} to check.
    * @param breakpoint The {@link IBreakpoint} to check.
    * @return {@code true} link represents breakpoint, {@code false} otherwise.
    */
   public boolean isBreakpointLink(ISEAnnotationLink link, IBreakpoint breakpoint) {
      return link instanceof BreakpointAnnotationLink &&
             ((BreakpointAnnotationLink)link).getBreakpoint() == breakpoint;
   }
}
