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
public class SearchNodePreorderIterator {
   /**
    * The next element or {@code null} if no more elements exists.
    */
   private Node next;
   
   /**
    * Constructor.
    * @param start The {@link Node} to iterate over its sub tree.
    */
   public SearchNodePreorderIterator(Node start) {
      this.next = start;
   }
   
   /**
    * Checks if more elements are available.
    * @return {@code true} has more elements, {@code false} has not more elements.
    */
   public boolean hasNext() {
      return next != null;
   }
   
   /**
    * Returns the next {@link Node} in the containment hierarchy.
    * @return The next {@link Node}.
    */
   public Node next() {
      Node oldNext = next;
      updateNext();
      return oldNext;
   }

   /**
    * Computes the next element and updates {@link #next()}.
    */
   protected void updateNext() {
      if (!next.leaf()) {
         next = next.child(0);
      }
      else {
         Node parent = next.parent();
         while (parent != null) {
            int childIndex = parent.getChildNr(next);
            int parentChildCount = parent.childrenCount();
            if (childIndex + 1 < parentChildCount) {
               next = parent.child(childIndex + 1);
               return; // done
            }
            else {
               next = parent;  // continue at parent
               parent = parent.parent();
            }
         }
         next = null;
      }
   }
}