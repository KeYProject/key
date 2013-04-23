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

package de.hentschel.visualdbc.interactive.proving.ui.command;

import org.eclipse.core.commands.AbstractHandler;
import org.eclipse.core.commands.ExecutionEvent;
import org.eclipse.core.commands.ExecutionException;
import org.eclipse.core.commands.IHandler;
import org.eclipse.core.commands.IHandler2;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.handlers.HandlerUtil;

import de.hentschel.visualdbc.interactive.proving.ui.util.LogUtil;

/**
 * Provides a basic implementation of:
 * <ul>
 *    <li>{@link IObjectActionDelegate}</li>
 *    <li>{@link IHandler}</li>
 *    <li>{@link IHandler2}</li>
 * </ul>
 * @author Martin Hentschel
 */
public abstract class AbstractCommand extends AbstractHandler implements IObjectActionDelegate {
   /**
    * The current {@link IAction}.
    */
   private IAction action;
   
   /**
    * The current {@link ISelection}.
    */
   private ISelection selection;
   
   /**
    * The defined target {@link IWorkbenchPart}.
    */
   private IWorkbenchPart targetPart;
   
   /**
    * The active {@link Shell}.
    */
   private Shell activeShell;

   /**
    * {@inheritDoc}
    */
   @Override
   public void run(IAction action) {
      this.action = action;
      saveExecute(selection);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void selectionChanged(IAction action, ISelection selection) {
      this.action = action;
      this.selection = selection;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setActivePart(IAction action, IWorkbenchPart targetPart) {
      this.action = action;
      this.targetPart = targetPart;
      if (this.targetPart != null) {
         this.activeShell = targetPart.getSite().getShell();
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Object execute(ExecutionEvent event) throws ExecutionException {
      this.selection = HandlerUtil.getCurrentSelection(event);
      this.activeShell = HandlerUtil.getActiveShell(event);
      this.targetPart = HandlerUtil.getActivePart(event);
      saveExecute(selection);
      return null;
   }
   
   /**
    * Save execution that can handles occurred {@link Exception}s.
    * @param selection The current {@link ISelection}.
    */
   protected void saveExecute(ISelection selection) {
      try {
         execute(selection);
      }
      catch (Exception e) {
         handleException(e);
      }
   }
   
   /**
    * Handles exceptions.
    * @param e The exception to handle.
    */
   protected void handleException(Exception e) {
      LogUtil.getLogger().openErrorDialog(getActiveShell(), e);
   }

   /**
    * Executes the command on the given {@link ISelection}.
    * @param selection The given {@link ISelection}.
    */
   protected abstract void execute(ISelection selection) throws Exception;

   /**
    * Returns the current {@link IAction}.
    * @return The current {@link IAction} or {@code null} if no one is defined.
    */
   protected IAction getAction() {
      return action;
   }

   /**
    * Returns the current {@link ISelection}.
    * @return The current {@link ISelection} or {@code null} if no one is defined.
    */
   protected ISelection getSelection() {
      return selection;
   }

   /**
    * Returns the defined target {@link IWorkbenchPart}.
    * @return The target {@link IWorkbenchPart} or {@code null} if no one is defined.
    */
   protected IWorkbenchPart getTargetPart() {
      return targetPart;
   }

   /**
    * Returns the active {@link Shell}.
    * @return The active {@link Shell} or {@code null} if no one is defined.
    */
   public Shell getActiveShell() {
      return activeShell;
   }
}