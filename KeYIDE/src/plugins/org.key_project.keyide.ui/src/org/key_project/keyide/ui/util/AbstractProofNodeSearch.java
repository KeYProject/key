package org.key_project.keyide.ui.util;

import java.util.HashSet;
import java.util.Set;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.Status;
import org.eclipse.core.runtime.jobs.Job;
import org.eclipse.ui.services.IDisposable;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofTreeAdapter;
import de.uka.ilkd.key.proof.ProofTreeEvent;
import de.uka.ilkd.key.proof.ProofTreeListener;
import de.uka.ilkd.key.util.NodePreorderIterator;
import de.uka.ilkd.key.util.SearchNodePreorderIterator;
import de.uka.ilkd.key.util.SearchNodeReversePreorderIterator;

/**
 * A basic {@link Job} to search proof tree {@link Node}s.
 * @author Martin Hentschel
 */
public abstract class AbstractProofNodeSearch extends Job implements IDisposable {
   /**
    * An optional {@link ISearchCallback}.
    */
   private final ISearchCallback callback;
   
   /**
    * The {@link IProofNodeSearchSupport} to use.
    */
   private final IProofNodeSearchSupport searchSupport;
   
   /**
    * The {@link Proof} to search in.
    */
   private final Proof proof;
   
   /**
    * The first found {@link Node}.
    */
   private Node firstFoundNode;
   
   /**
    * All found {@link Node}s.
    */
   private Set<Node> foundNodes = new HashSet<Node>();
   
   /**
    * The last found {@link Node}.
    */
   private Node lastFoundNode;
   
   /**
    * Listens for changes of the proof tree.
    */
   private final ProofTreeListener proofTreeListener = new ProofTreeAdapter() {

      @Override
      public void proofExpanded(ProofTreeEvent e) {
         handleProofChanged();
      }

      @Override
      public void proofPruned(ProofTreeEvent e) {
         handleProofChanged();
      }

      @Override
      public void proofStructureChanged(ProofTreeEvent e) {
         handleProofChanged();
      }

      @Override
      public void proofClosed(ProofTreeEvent e) {
         handleProofChanged();
      }

      @Override
      public void proofGoalRemoved(ProofTreeEvent e) {
         handleProofChanged();
      }

      @Override
      public void proofGoalsAdded(ProofTreeEvent e) {
         handleProofChanged();
      }

      @Override
      public void proofGoalsChanged(ProofTreeEvent e) {
         handleProofChanged();
      }

      @Override
      public void smtDataUpdate(ProofTreeEvent e) {
         handleProofChanged();
      }
   };

   /**
    * Constructor.
    * @param callback The optional {@link ISearchCallback} to use.
    * @param searchSupport The {@link IProofNodeSearchSupport} to use.
    * @param proof The {@link Proof} to search in.
    * @param name The name of this {@link Job}.
    */
   public AbstractProofNodeSearch(ISearchCallback callback, IProofNodeSearchSupport searchSupport, Proof proof, String name) {
      super(name);
      this.callback = callback;
      this.searchSupport = searchSupport;
      this.proof = proof;
      if (proof != null) {
         proof.addProofTreeListener(proofTreeListener);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected IStatus run(IProgressMonitor monitor) {
      try {
         SWTUtil.checkCanceled(monitor);
         if (proof != null) {
            // Perform search and collect previous nodes
            NodePreorderIterator iterator = new NodePreorderIterator(proof.root());
            while (iterator.hasNext()) {
               SWTUtil.checkCanceled(monitor);
               Node next = iterator.next();
               if (acceptNode(next)) {
                  if (firstFoundNode == null) {
                     firstFoundNode = next;
                  }
                  foundNodes.add(next);
                  lastFoundNode = next;
               }
            }
            // Show first result
            if (searchSupport != null) {
               searchSupport.jumpToNextResult();
            }
         }
         return Status.OK_STATUS;
      }
      catch (OperationCanceledException e) {
         firstFoundNode = null;
         lastFoundNode = null;
         foundNodes.clear();
         return Status.CANCEL_STATUS;
      }
      finally {
         if (callback != null) {
            callback.searchCompleted(this);
         }
      }
   }

   /**
    * Checks if the given {@link Node} is part of the search result.
    * @param node The {@link Node} to check.
    * @return {@code true} is part of search result, {@code false} otherwise.
    */
   protected abstract boolean acceptNode(Node node);

   /**
    * Checks if the search is completed.
    * @return {@code true} completed, {@code false} not completed.
    */
   public boolean isSearchComplete() {
      return lastFoundNode != null;
   }
   
   /**
    * Checks if the given {@link Node} is part of the result.
    * @param node The {@link Node} to check.
    * @return {@code true} part of result, {@code false} otherwise.
    */
   public boolean containsResult(Node node) {
      return foundNodes.contains(node);
   }

   /**
    * Checks if the search result is empty.
    * @return {@code true} search result is empty, {@code false} otherwise.
    */
   public boolean isResultEmpty() {
      return foundNodes.isEmpty();
   }

   /**
    * When the proof has changed.
    */
   protected void handleProofChanged() {
      if (getState() == Job.RUNNING) {
         cancel();
      }
      schedule();
   }
   
   /**
    * Returns the next {@link Node} part of the search result below the given {@link Node}.
    * @param current The given {@link Node}.
    * @return The next {@link Node} part of the search result or {@code null} if the search result is empty.
    */
   public Node getNextResult(Node current) {
      SearchNodePreorderIterator iterator = new SearchNodePreorderIterator(current);
      // Skip current node
      if (iterator.hasNext()) {
         iterator.next();
      }
      // Search next result
      Node foundNode = null;
      while (foundNode == null && iterator.hasNext()) {
         Node next = iterator.next();
         if (foundNodes.contains(next)) {
            foundNode = next;
         }
      }
      // Return result;
      return foundNode != null ? foundNode : firstFoundNode;
   }
   
   /**
    * Returns the previous {@link Node} part of the search result above the given {@link Node}.
    * @param current The given {@link Node}.
    * @return The previous {@link Node} part of the search result or {@code null} if the search result is empty.
    */
   public Node getPreviousResult(Node current) {
      SearchNodeReversePreorderIterator iterator = new SearchNodeReversePreorderIterator(current);
      // Skip current node
      if (iterator.hasPrevious()) {
         iterator.previous();
      }
      // Search next result
      Node foundNode = null;
      while (foundNode == null && iterator.hasPrevious()) {
         Node next = iterator.previous();
         if (foundNodes.contains(next)) {
            foundNode = next;
         }
      }
      // Return result;
      return foundNode != null ? foundNode : lastFoundNode;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (proof != null) {
         proof.removeProofTreeListener(proofTreeListener);
      }
   }
   
   /**
    * Allows to detect when the search completes.
    * @author Martin Hentschel
    */
   public static interface ISearchCallback {
      /**
       * When the search completes.
       * @param search The completed search.
       */
      public void searchCompleted(AbstractProofNodeSearch search);
   }
}
