package org.key_project.sed.core.annotation.impl;

import org.key_project.sed.core.annotation.ISEDAnnotation;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.util.SEDAnnotationUtil;

/**
 * The {@link ISEDAnnotation} representing a search.
 * @author Martin Hentschel
 * @see SearchAnnotationType
 */
public class SearchAnnotation extends AbstractSEDAnnotation {
   /**
    * Property {@link #getSearch()}.
    */
   public static final String PROP_SEARCH = "search";
   
   /**
    * The text to search.
    */
   private String search;
   
   /**
    * Constructor.
    */
   public SearchAnnotation() {
      super(SEDAnnotationUtil.getAnnotationtype(SearchAnnotationType.TYPE_ID), true);
   }

   /**
    * Returns the text to search.
    * @return The text to search.
    */
   public String getSearch() {
      return search;
   }

   /**
    * Sets the text to search.
    * @param search The text to search.
    */
   public void setSearch(String search) {
      String oldSearch = getSearch();
      this.search = search;
      firePropertyChange(PROP_SEARCH, oldSearch, getSearch());
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean canDelete(ISEDDebugTarget target) {
      return true;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public String toString() {
      return "Search: " + getSearch();
   }
}
