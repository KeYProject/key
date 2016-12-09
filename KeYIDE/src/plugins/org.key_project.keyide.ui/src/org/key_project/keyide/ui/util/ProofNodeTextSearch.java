package org.key_project.keyide.ui.util;

import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.jface.viewers.ILabelProvider;
import org.key_project.keyide.ui.util.AbstractProofNodeSearch.ISearchCallback;
import org.key_project.util.java.StringUtil;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;

/**
 * A {@link Job} to search proof tree {@link Node}s by their label in the user interface.
 * @author Martin Hentschel
 */
public class ProofNodeTextSearch extends AbstractProofNodeSearch {
   /**
    * The {@link ILabelProvider} to use.
    */
   private final ILabelProvider labelProvider;
   
   /**
    * The text to search.
    */
   private final String searchText;

   /**
    * Constructor.
    * @param callback The optional {@link ISearchCallback} to use.
    * @param searchSupport The {@link IProofNodeSearchSupport} to use.
    * @param labelProvider The {@link ILabelProvider} to use.
    * @param proof The {@link Proof} to search in.
    * @param searchText The text to search.
    */
   public ProofNodeTextSearch(ISearchCallback callback, 
                              IProofNodeSearchSupport searchSupport, 
                              ILabelProvider labelProvider, 
                              Proof proof, 
                              String searchText) {
      super(callback, searchSupport, proof, "Searching for \"" + searchText + "\".");
      assert labelProvider != null;
      this.labelProvider = labelProvider;
      this.searchText = StringUtil.toLowerCase(searchText);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected boolean acceptNode(Node next) {
      String nodeText = StringUtil.toLowerCase(labelProvider.getText(next));
      return nodeText != null && nodeText.contains(searchText);
   }
}
