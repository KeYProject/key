/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.util;

import org.eclipse.jdt.core.dom.ASTNode;
import org.eclipse.jdt.core.dom.ASTVisitor;

/**
 * Instances of this {@link ASTVisitor} are used to find {@link ASTNode} in 
 * the AST that end index matches a defined one.
 * @author Martin Hentschel
 */
public class ASTNodeByEndIndexSearcher extends ASTVisitor {
   /**
    * The end index of the node to search.
    */
   private int endIndex;
   
   /**
    * The found node with the given end index.
    */
   private ASTNode foundNode;

   /**
    * Constructor.
    * @param endIndex The end index of the node to search.
    */
   public ASTNodeByEndIndexSearcher(int endIndex) {
      this.endIndex = endIndex;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean preVisit2(ASTNode node) {
      if (node != null) {
         int nodeStartIndex = node.getStartPosition();
         int nodeEndIndex = nodeStartIndex + node.getLength();
         if (endIndex == nodeEndIndex) {
            foundNode = node;
         }
         return foundNode == null &&
                nodeStartIndex <= endIndex && 
                nodeEndIndex >= endIndex;
      }
      else {
         return false;
      }
   }

   /**
    * Returns the found node.
    * @return The found node.
    */
   public ASTNode getFoundNode() {
      return foundNode;
   }
   
   /**
    * Searches an {@link ASTNode} from the given root which end index
    * matches the defined one.
    * @param root The root node to start search.
    * @param endIndex The end index of the node to search.
    * @return The found {@link ASTNode} with the given end index or {@code null} if no node was found.
    */
   public static ASTNode search(ASTNode root, int endIndex) {
      if (root != null) {
         ASTNodeByEndIndexSearcher searcher = new ASTNodeByEndIndexSearcher(endIndex); 
         root.accept(searcher);
         return searcher.getFoundNode();
      }
      else {
         return null;
      }
   }
}