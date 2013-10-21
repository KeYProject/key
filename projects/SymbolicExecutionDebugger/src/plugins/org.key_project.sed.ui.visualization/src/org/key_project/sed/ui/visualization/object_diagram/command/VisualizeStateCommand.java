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

package org.key_project.sed.ui.visualization.object_diagram.command;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.handlers.HandlerUtil;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.visualization.object_diagram.editor.ReadonlyObjectDiagramEditor;
import org.key_project.sed.ui.visualization.object_diagram.util.ObjectDiagramUtil;
import org.key_project.util.eclipse.swt.SWTUtil;

/**
 * This {@link IHandler} visualizes the state of each selected
 * {@link IStackFrame} which provides a state via {@link IStackFrame#getVariables()}
 * as Object Diagram.
 * @author Martin Hentschel
 */
public class VisualizeStateCommand extends AbstractHandler {
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
               visualizeState((ISEDDebugNode)element,
                              HandlerUtil.getActivePart(event).getSite().getPage());
            }
         }
         return null;
      }
      catch (Exception e) {
         throw new ExecutionException("Can't visualize state.", e);
      }
   }
   
   /**
    * Checks if the given {@link Object} can be visualized in an object diagram.
    * @param element The {@link Object} to check.
    * @return {@code true} can visualize in an object diagram, {@code false} can not visualize.
    * @throws DebugException Occurred Exception.
    */
   public static boolean canVisualize(Object element) throws DebugException {
      return element instanceof IStackFrame && 
             element instanceof ISEDDebugNode &&
             ((IStackFrame)element).hasVariables();
   }

   /**
    * Visualizes the state of the given {@link ISEDDebugNode} which
    * is also an {@link IStackFrame}.
    * @param node The {@link ISEDDebugNode} to visualize.
    * @param activePage The active {@link IWorkbenchPage}.
    * @throws Exception Occurred Exception.
    */
   public static void visualizeState(ISEDDebugNode node,
                                     IWorkbenchPage activePage) throws Exception {
      // Open editor
      ReadonlyObjectDiagramEditor readonlyEditor = ReadonlyObjectDiagramEditor.openEditor(activePage, node.getName(), node.getId());
      // Generate object diagram if not already available
      if (!ObjectDiagramUtil.hasModel(readonlyEditor.getDiagramTypeProvider().getDiagram())) {
         readonlyEditor.generateObjectDiagram(node);
      }
   }
}