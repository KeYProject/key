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

package org.key_project.util.test.editor;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Text;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.part.EditorPart;
import org.key_project.util.eclipse.view.editorInView.IGlobalEnablement;

/**
 * A simple {@link IEditorPart} which contains one {@link Text} instance.
 * @author Martin Hentschel
 */
public class TextControlEditor extends EditorPart implements IGlobalEnablement {
   /**
    * The contained {@link Text} instance.
    */
   private Text text;

   /**
    * The global enabled state.
    */
   private boolean globalEnabled;
   
   /**
    * Dirty flag.
    */
   private boolean dirty = false;
   
   /**
    * Counts the calls of {@link #doSave(IProgressMonitor)}.
    */
   private int saveCount = 0;
   
   /**
    * Counts the calls of {@link #doSaveAs()}.
    */
   private int saveAsCount = 0;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void doSave(IProgressMonitor monitor) {
      saveCount++;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void doSaveAs() {
      saveAsCount++;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IEditorSite site, IEditorInput input) throws PartInitException {
      setSite(site);
      if (input != null) {
         setInput(input);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDirty() {
      return dirty;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isSaveAsAllowed() {
      return true;
   }

   /**
    * Defines if this editor is dirty or not.
    * @param dirty {@code true} editor is dirty, {@code false} editor is not dirty.
    */
   public void setDirty(boolean dirty) {
      this.dirty = dirty;
      firePropertyChange(PROP_DIRTY);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void createPartControl(Composite parent) {
      text = new Text(parent, SWT.BORDER);
      text.setText("This is an Editor.");
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setFocus() {
      text.setFocus();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isGlobalEnabled() {
      return globalEnabled;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void setGlobalEnabled(boolean globalEnabled) {
      this.globalEnabled = globalEnabled;
   }

   /**
    * Returns how often save ({@link #doSave(IProgressMonitor)}) was called.
    * @return The number of called saves.
    */
   public int getSaveCount() {
      return saveCount;
   }

   /**
    * Returns how often save as ({@link #doSaveAs()}) was called.
    * @return The number of called saves as .
    */
   public int getSaveAsCount() {
      return saveAsCount;
   }
}