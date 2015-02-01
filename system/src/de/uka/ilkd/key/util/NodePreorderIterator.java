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

import java.util.Iterator;

import de.uka.ilkd.key.proof.Node;

/**
 * <p>
 * Iterates preorder over the whole sub tree of a given {@link Node}.
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
public class NodePreorderIterator {
   /**
    * The element at that the iteration has started used as end condition
    * to make sure that only over the subtree of the element is iterated.
    */
   private Node start;

   /**
    * The next element or {@code null} if no more elements exists.
    */
   private Node next;
   
   /**
    * Constructor.
    * @param start The {@link Node} to iterate over its sub tree.
    */
   public NodePreorderIterator(Node start) {      
      this.start = start;
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
      Node newNext = null;
      if (next.childrenCount() >= 1) {
         newNext = next.child(0);
      }
      else {
         newNext = getNextOnParent(next);
      }
      this.next = newNext;
   }
   
   /**
    * Returns the next element to select if all children of the given
    * {@link Node} are visited.
    * @param node The visited {@link Node}.
    * @return The next {@link Node} to visit.
    */
   protected Node getNextOnParent(Node node) {
      Node parent = node.parent();
      while (parent != null) {
         boolean nodeFound = false; // Indicates that node was found on the parent.
         Iterator<Node> parentChildIter = parent.childrenIterator();
         Node nextChildOnParent = null; // The next child on the parent or the last child after iteration has finished
         while (parentChildIter.hasNext()) {
            nextChildOnParent = parentChildIter.next();
            if (nextChildOnParent == start) {
               return null;
            }
            if (nodeFound) {
               return nextChildOnParent;
            }
            if (nextChildOnParent == node) {
               nodeFound = true;
            }
         }
         if (nextChildOnParent != start) {
            node = parent; // Continue search on parent without recursive call!
            parent = parent.parent(); 
         }
         else {
            return null;
         }
      }
      return null; // No more parents available.
   }
}