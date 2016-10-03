package org.key_project.keyide.ui.util;

/**
 * The interface to perform a search of proof tree nodes.
 * @author Martin Hentschel
 */
public interface IProofNodeSearchSupport {
   /**
    * Opens the search.
    */
   public void openSearchPanel();
   
   /**
    * Closes the search.
    */
   public void closeSearchPanel();
   
   /**
    * Searches for the given text.
    * @param text The text to search.
    */
   public void searchText(String text);
   
   /**
    * Jump to the previous result.
    */
   public void jumpToPreviousResult();
   
   /**
    * Jump to the next result.
    */
   public void jumpToNextResult();
}
