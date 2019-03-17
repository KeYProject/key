// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

import de.uka.ilkd.key.proof.Node;

/**
 * <p>
 * Iterates reverse preorder over the whole tree starting at a given {@link Node}.
 * </p>
 * <p>
 * Instances of this class should always be used instead of recursive method
 * calls because they cause {@link StackOverflowError}s even in small programs.
 * </p>
 * <p>
 * <b>Attention: </b>The iteration process does not take care of changes in
 * the model. If the containment hierarchy changes during iteration it is possible
 * that elements are left or visited multiple times. For this reason it is forbidden
 * to change the model during iteration. But the developer has to take care about it.
 * </p>
 * @author Martin Hentschel
 */
public class SearchNodeReversePreorderIterator {
   /**
    * The previous element or {@code null} if no more elements exists.
    */
   private Node previous;
   
   /**
    * Constructor.
    * @param start The {@link Node} to iterate over its sub tree.
    */
   public SearchNodeReversePreorderIterator(Node start) {
      this.previous = start;
   }
   
   /**
    * Checks if more elements are available.
    * @return {@code true} has more elements, {@code false} has not more elements.
    */
   public boolean hasPrevious() {
      return previous != null;
   }
   
   /**
    * Returns the next {@link Node} in the containment hierarchy.
    * @return The next {@link Node}.
    */
   public Node previous() {
      Node oldPrevious = previous;
      updatePrevious();
      return oldPrevious;
   }

   /**
    * Computes the previous element and updates {@link #previous()}.
    */
   protected void updatePrevious() {
      Node parent = previous.parent();
      if (parent != null) {
         int index = parent.getChildNr(previous);
         if (index >= 1) {
            previous = lastLeaf(parent.child(index - 1));
         }
         else {
            previous = parent;
         }
      }
      else {
         previous = null;
      }
   }

   /**
    * Returns the last leaf node.
    * @param node The current {@link Node}.
    * @return The last leaf of the given {@link Node}.
    */
   protected Node lastLeaf(Node node) {
      int childCount = node.childrenCount();
      while (childCount >= 1) {
         node = node.child(childCount - 1);
         childCount = node.childrenCount();
      }
      return node;
   }
}