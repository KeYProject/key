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

package org.key_project.sed.key.ui.visualization.execution_tree.command;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.debug.core.DebugException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.sed.key.core.model.IKeYSEDDebugNode;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.sed.key.ui.visualization.object_diagram.editor.ConfigurationObjectDiagramEditor;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionStateNode;

/**
 * This {@link IHandler} visualizes the configurations of selected {@link IKeYSEDDebugNode}s.
 * @author Martin Hentschel
 */
public class VisualizeConfigurationsCommand extends AbstractHandler {
   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      try {
         ISelection selection = HandlerUtil.getCurrentSelection(event);
         Object[] elements = SWTUtil.toArray(selection);
         for (Object element : elements) {
            if (canVisualize(element)) {
               visualizeConfigurations((IKeYSEDDebugNode<?>)element,
                              HandlerUtil.getActivePart(event).getSite().getPage());
            }
         }
         return null;
      }
      catch (Exception e) {
         throw new ExecutionException("Can't visualize configurations.", e);
      }
   }
   
   /**
    * Checks if the given {@link Object} can be visualized in an object diagram.
    * @param element The {@link Object} to check.
    * @return {@code true} can visualize in an object diagram, {@code false} can not visualize.
    * @throws DebugException Occurred Exception.
    */
   public static boolean canVisualize(Object element) throws DebugException {
      try {
         if (element instanceof IKeYSEDDebugNode<?>) {
            IKeYSEDDebugNode<?> node = (IKeYSEDDebugNode<?>)element;
            return !node.getExecutionNode().isDisposed() &&
                   node.getExecutionNode() instanceof IExecutionStateNode<?> &&
                   node.getExecutionNode().getPathCondition().op() != Junctor.FALSE;
         }
         else {
            return false;
         }
      }
      catch (ProofInputException e) {
         throw new DebugException(LogUtil.getLogger().createErrorStatus(e));
      }
   }

   /**
    * Visualizes the configurations of the given {@link IKeYSEDDebugNode}.
    * @param node The {@link IKeYSEDDebugNode} to visualize.
    * @param activePage The active {@link IWorkbenchPage}.
    * @throws Exception Occurred Exception.
    */
   public static void visualizeConfigurations(IKeYSEDDebugNode<?> node,
                                              IWorkbenchPage activePage) throws Exception {
      // Open editor
      ConfigurationObjectDiagramEditor configurationsEditor = ConfigurationObjectDiagramEditor.openEditor(activePage, node.getName(), node.getId() + "_configurations");
      // Generate object diagram if not already available
      if (!ObjectDiagramUtil.hasModel(configurationsEditor.getDiagramTypeProvider().getDiagram())) {
         configurationsEditor.generateConfigurationsDiagram(node);
      }
   }
}