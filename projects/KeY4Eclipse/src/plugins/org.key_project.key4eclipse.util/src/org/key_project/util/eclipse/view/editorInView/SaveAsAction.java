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

package org.key_project.util.eclipse.view.editorInView;

import org.eclipse.core.commands.CommandEvent;
import org.eclipse.core.commands.ICommandListener;
import org.eclipse.ui.IPropertyListener;
import org.eclipse.ui.ISaveablePart;
import org.eclipse.ui.IWorkbenchCommandConstants;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.internal.IWorkbenchHelpContextIds;
import org.eclipse.ui.internal.WorkbenchMessages;
import org.eclipse.ui.internal.actions.CommandAction;
import org.eclipse.ui.services.IDisposable;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * This save as action is similar to created commands of
 * {@link ActionFactory#SAVE_AS#create(org.eclipse.ui.IWorkbenchWindow)} but
 * does not delegate the save as request ({@link ISaveablePart#doSaveAs()})
 * to the active {@link IWorkbenchPart}. Instead it always delegated to 
 * a given fixed {@link IWorkbenchPart}.
 * @author Martin Hentschel
 */
// TODO: Implement tests
@SuppressWarnings("restriction")
public class SaveAsAction extends CommandAction implements IDisposable {
   /**
    * The provided {@link ICommandListener} of {@link #getCommandListener()}.
    */
   private ICommandListener commandListener;
   
   /**
    * The fixed {@link IWorkbenchPart} to call {@link ISaveablePart#doSaveAs()} on. 
    */
   private IWorkbenchPart fixedPart;

   /**
    * Listens for changes on {@link #fixedPart}.
    */
   private IPropertyListener fixedPartListener = new IPropertyListener() {
      @Override
      public void propertyChanged(Object source, int propId) {
         handleFixedPartPropertyChanged(source, propId);
      }
   };
   
   /**
    * Constructor.
    * @param fixedPart The fixed {@link IWorkbenchPart} to call {@link ISaveablePart#doSaveAs()} on.
    */
   public SaveAsAction(IWorkbenchPart fixedPart) {
      super(fixedPart.getSite().getPage().getWorkbenchWindow(), IWorkbenchCommandConstants.FILE_SAVE_AS);
      this.fixedPart = fixedPart;
      setText(WorkbenchMessages.SaveAs_text);
      setToolTipText(WorkbenchMessages.SaveAs_toolTip);
      fixedPart.getSite().getPage().getWorkbenchWindow().getWorkbench().getHelpSystem().setHelp(this, IWorkbenchHelpContextIds.SAVE_AS_ACTION);
      setId("saveAs");
      fixedPart.addPropertyListener(fixedPartListener);
   }

   /**
    * When a property of {@link #fixedPart} has changed.
    * @param source The event's source.
    * @param propId The ID of the changed property.
    */
   protected void handleFixedPartPropertyChanged(Object source, int propId) {
      if (ISaveablePart.PROP_DIRTY == propId) {
         setEnabled(isSaveAsAllowed());
      }
   }
   
   /**
    * Checks if save as is allowed or not.
    * @return {@code true} allowed, {@code false} forbidden
    */
   protected boolean isSaveAsAllowed() {
      if (fixedPart instanceof ISaveablePart) {
         return ((ISaveablePart) fixedPart).isSaveAsAllowed();
      }
      else {
         return false;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      fixedPart.removePropertyListener(fixedPartListener);
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setEnabled(boolean enabled) {
      super.setEnabled(enabled);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected ICommandListener getCommandListener() {
      if (commandListener == null) {
         commandListener = new ICommandListener() {
            public void commandChanged(CommandEvent commandEvent) {
               if (ObjectUtil.equals(fixedPart, WorkbenchUtil.getActivePart())) {
                  if (commandEvent.isHandledChanged() || commandEvent.isEnabledChanged()) {
                     if (commandEvent.getCommand().isDefined()) {
                        setEnabled(isSaveAsAllowed());
                     }
                  }
               }
            }
         };
      }
      return commandListener;
   }
}