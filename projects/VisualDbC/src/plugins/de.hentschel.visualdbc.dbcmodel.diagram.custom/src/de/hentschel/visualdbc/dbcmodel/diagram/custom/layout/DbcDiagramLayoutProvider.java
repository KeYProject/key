/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

package de.hentschel.visualdbc.dbcmodel.diagram.custom.layout;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.draw2d.graph.DirectedGraph;
import org.eclipse.emf.ecore.EObject;
import org.eclipse.gef.ConnectionEditPart;
import org.eclipse.gef.GraphicalEditPart;
import org.eclipse.gef.commands.Command;
import org.eclipse.gmf.runtime.common.core.service.IOperation;
import org.eclipse.gmf.runtime.diagram.ui.providers.TopDownProvider;
import org.eclipse.gmf.runtime.diagram.ui.services.layout.ILayoutNode;
import org.eclipse.gmf.runtime.diagram.ui.services.layout.ILayoutNodeOperation;
import org.eclipse.gmf.runtime.diagram.ui.services.layout.LayoutType;
import org.eclipse.gmf.runtime.draw2d.ui.graph.ConstantSizeNode;
import org.eclipse.gmf.runtime.notation.Diagram;
import org.eclipse.gmf.runtime.notation.View;

import de.hentschel.visualdbc.dbcmodel.AbstractDbcType;
import de.hentschel.visualdbc.dbcmodel.diagram.custom.util.CustomPreferences;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcConstructorEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcInvariantEditPart;
import de.hentschel.visualdbc.dbcmodel.diagram.edit.parts.DbcMethodEditPart;

/**
 * <p>
 * A custom layout provider to arrange the elements in an DbC model diagram.
 * </p>
 * <p>
 * The difference is that optionally methods, constructors and invariants
 * are ordered in a vertical instead of the horizontal line.
 * </p>
 * @author Martin Hentschel
 */
public class DbcDiagramLayoutProvider extends TopDownProvider {
   /**
    * <p>
    * Constant for the default layout hint.
    * </p>
    * <p>
    * see: <a href="http://wiki.eclipse.org/GMF_Tutorial_Part_3">http://wiki.eclipse.org/GMF_Tutorial_Part_3</a>
    * </p>
    */
   public static String DEFAULT_LAYOUT = "Default";
   
   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   protected Command update_diagram(GraphicalEditPart diagramEP, DirectedGraph g, boolean isLayoutForSelected) {
      if (isPostProcessingActivated()) {
         postProcessGraph(g); // Modify already computed target diagram layout
      }
      return super.update_diagram(diagramEP, g, isLayoutForSelected); // Create command to layout diagram
   }

   /**
    * <p>
    * The given {@link DirectedGraph} contains the default computed target layout
    * for the diagram. This layout is one horizontal line from left to right
    * with all elements if no connection exists between theme. If connection
    * exists the linked nodes are reorganized in the horizontal line.
    * </p>
    * <p>
    * This methods reorganizes the elements in a type main compartment.
    * Methods, constructors and invariants are not longer arranged horizontal.
    * Instead of this they are arranged vertical.
    * </p>
    * <p>
    * Inner types are in the top of the main compartment. Because of their
    * possible connections (extends, implements) this sub diagram is handled
    * as an offset for vertical arranged methods, constructors and invariants.
    * </p>
    * @param g The already computed graph with the target diagram layout.
    */
   protected void postProcessGraph(DirectedGraph g) {
      // Create mapping for domain objects to their target layout node
      Map<EObject, ConstantSizeNode> mapping = new HashMap<EObject, ConstantSizeNode>();
      for (Object node : g.nodes) {
         Assert.isTrue(node instanceof ConstantSizeNode);
         ConstantSizeNode cNode = (ConstantSizeNode)node;
         IAdaptable data = (IAdaptable)cNode.data;
         mapping.put((EObject)data.getAdapter(EObject.class), cNode);
      }
      // Rearrange methods, constructors and invariants.
      Set<ConstantSizeNode> rearrangedNodes = new HashSet<ConstantSizeNode>();
      for (Object node : g.nodes) {
         Assert.isTrue(node instanceof ConstantSizeNode);
         ConstantSizeNode cNode = (ConstantSizeNode)node;
         if (cNode.data instanceof DbcMethodEditPart ||
             cNode.data instanceof DbcConstructorEditPart ||
             cNode.data instanceof DbcInvariantEditPart) {
            // Compute offset for inner types
            int typeOffset = computeTypeOffset(mapping, cNode);
            // Rearrange the current element
            updateVertical(typeOffset, rearrangedNodes, cNode);
         }
      }
   }

   /**
    * Computes the type offset.
    * @param mapping The mapping to use.
    * @param cNode The current node to compute the type offset-
    * @return The computed type offset.
    */
   protected int computeTypeOffset(Map<EObject, ConstantSizeNode> mapping, ConstantSizeNode cNode) {
      EObject element = (EObject)((IAdaptable)cNode.data).getAdapter(EObject.class);
      EObject parent = element.eContainer();
      int max = 0;
      if (parent instanceof AbstractDbcType) {
         for (AbstractDbcType type : ((AbstractDbcType)parent).getTypes()) {
            ConstantSizeNode node = mapping.get(type);
            Assert.isNotNull(node);
            int currentMax = node.y + node.height;
            if (currentMax > max) {
               max = currentMax;
            }
         }
      }
      return max;
   }

   /**
    * Rearrange the node.
    * @param typeOffset The type offset to use.
    * @param rearrangedNodes Contains the already horizontal to vertical rearranged elements.
    * @param cNode The current node to rearrange.
    */
   protected void updateVertical(int typeOffset, Set<ConstantSizeNode> rearrangedNodes, ConstantSizeNode cNode) {
      // Rearrange node from horizontal into vertical layout if not already done.
      if (!rearrangedNodes.contains(cNode)) {
         int helper = cNode.x;
         cNode.x = cNode.y;
         cNode.y = helper;
         rearrangedNodes.add(cNode);
      }
      // Update y position to minimize the used space
      if (cNode.getLeft() != null) {
         if (cNode.getLeft() != null) {
            EObject leftObj = (EObject)((IAdaptable)cNode.getLeft().data).getAdapter(EObject.class);
            if (leftObj instanceof AbstractDbcType) {
               cNode.y = typeOffset + getVerticalSpacing();
            }
            else {
               cNode.y = maxNewY(cNode);
            }
         }
         else {
            cNode.y = maxNewY(cNode);
         }
      }
      // Update the y position of right/bottom elements to minimize used space
      if (cNode.getRight() != null) {
         updateVertical(typeOffset, rearrangedNodes, (ConstantSizeNode)cNode.getRight());
      }
   }
   
   /**
    * Computes the maximal y coordinate from the previous elements.
    * @param cNode The current node.
    * @return The maximal y coordinate from the previous elements
    */
   protected int maxNewY(ConstantSizeNode cNode) {
      if (cNode.getLeft() != null) {
         int maxThis = cNode.getLeft().y + cNode.getLeft().height + getVerticalSpacing();
         int maxLeft = maxNewY((ConstantSizeNode)cNode.getLeft());
         return maxThis > maxLeft ? maxThis : maxLeft;
      }
      else {
         return 0;
      }
   }
   
   /**
    * The vertical spacing between elements.
    * @return The vertical spacing between rearranged elements.
    */
   public int getVerticalSpacing() {
      return CustomPreferences.getVerticalSpacing();
   }

   /**
    * Checks if post processing is activated or not.
    * @return {@code true} = do post processing, {@code false} = no post processing.
    */
   public boolean isPostProcessingActivated() {
      return CustomPreferences.isUseCustomLayout();
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("restriction")
   @Override
   protected boolean layoutTopDown(ConnectionEditPart poly) {
      return isPostProcessingActivated() ? true : super.layoutTopDown(poly);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean provides(IOperation operation) {
      if (isPostProcessingActivated()) {
         // enable this provider only on DbC Model diagrams
         // see: http://wiki.eclipse.org/GMF_Tutorial_Part_3
         if (operation instanceof ILayoutNodeOperation) {
            Iterator<?> nodes = ((ILayoutNodeOperation) operation).getLayoutNodes().listIterator();
            if (nodes.hasNext()) {
               View node = ((ILayoutNode) nodes.next()).getNode();
               Diagram container = node.getDiagram();
               if (container == null || !(container.getType().equals("DbC")))
                  return false;
            }
         }
         else {
            return false;
         }
         IAdaptable layoutHint = ((ILayoutNodeOperation) operation).getLayoutHint();
         String layoutType = (String) layoutHint.getAdapter(String.class);
         return LayoutType.DEFAULT.equals(layoutType);
      }
      else {
         return false;
      }
   }
}