package org.key_project.sed.core.annotation.impl;

import org.eclipse.core.runtime.Assert;
import org.eclipse.debug.core.DebugException;
import org.eclipse.swt.graphics.RGB;
import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.annotation.ISEDAnnotationLink;
import org.key_project.sed.core.annotation.ISEDAnnotationType;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.util.java.StringUtil;

/**
 * The {@link ISEDAnnotationType} used for searches.
 * @author Martin Hentschel
 * @see SearchAnnotation
 */
public class SearchAnnotationType extends AbstractSEDAnnotationType {
   /**
    * The ID of this annotation type.
    */
   public static final String TYPE_ID = "org.key_project.sed.core.annotationType.search";
   
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
      return "Search";
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
      return new RGB(0, 128, 192); // Nice blue
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
   public SearchAnnotation createAnnotation() {
      return new SearchAnnotation();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public ISEDAnnotationLink createLink(ISEDAnnotation source, ISEDDebugNode target) {
      return new SearchAnnotationLink(source, target);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String saveAnnotation(ISEDAnnotation annotation) {
      Assert.isTrue(annotation instanceof SearchAnnotation);
      return ((SearchAnnotation)annotation).getSearch();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void restoreAnnotation(ISEDAnnotation annotation, String savedContent) {
      Assert.isTrue(annotation instanceof SearchAnnotation);
      ((SearchAnnotation)annotation).setSearch(savedContent);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void initializeNode(ISEDDebugNode node, ISEDAnnotation annotation) throws DebugException {
      Assert.isTrue(annotation instanceof SearchAnnotation);
      if (accept(node, ((SearchAnnotation)annotation).getSearch())) {
         node.addAnnotationLink(createLink(annotation, node));
      }
   }
   
   /**
    * Checks if the given {@link ISEDDebugNode} matches the search criteria.
    * @param node The {@link ISEDDebugNode} to check.
    * @param search The text to search.
    * @return {@code true} match, {@code false} not match.
    * @throws DebugException Occurred Exception.
    */
   public static boolean accept(ISEDDebugNode node, String search) throws DebugException {
      if (node != null) {
         String name = node.getName();
         return StringUtil.contains(name, search);
      }
      else {
         return true;
      }
   }
}
