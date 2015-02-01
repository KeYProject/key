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

package org.key_project.util.eclipse.view.editorInView;

import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.dynamichelpers.IExtensionTracker;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IEditorReference;
import org.eclipse.ui.INavigationHistory;
import org.eclipse.ui.IPartListener;
import org.eclipse.ui.IPartListener2;
import org.eclipse.ui.IPerspectiveDescriptor;
import org.eclipse.ui.IReusableEditor;
import org.eclipse.ui.ISelectionListener;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IViewSite;
import org.eclipse.ui.IWorkbenchPage;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.IWorkbenchPartReference;
import org.eclipse.ui.IWorkbenchWindow;
import org.eclipse.ui.IWorkingSet;
import org.eclipse.ui.MultiPartInitException;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.internal.PartListenerList;
import org.eclipse.ui.internal.PartListenerList2;
import org.eclipse.ui.services.IDisposable;
import org.key_project.util.java.ObjectUtil;

/**
 * <p>
 * Implementation of {@link IWorkbenchPage} which can be used to show an
 * {@link IEditorPart} in an {@link IViewPart}.
 * </p>
 * <p>
 * The default implementation of such view is provided in {@link AbstractEditorInViewView}.
 * </p>
 * @author Martin Hentschel
 * @see AbstractEditorInViewView
 * @see EditorInViewEditorSite
 */
@SuppressWarnings("restriction")
public class EditorInViewWorkbenchPage implements IWorkbenchPage, IDisposable {
   /**
    * The {@link IViewSite} of an {@link IViewPart} which contains an {@link IEditorPart}.
    */
   private IViewSite wrapperViewSite;

   /**
    * The {@link IEditorPart} which is shown in the {@link IViewPart} of {@link #wrapperViewSite}.
    */
   private IEditorPart wrappedEditorPart;
   
   /**
    * Internal management of {@link IPartListener}.
    */
   private PartListenerList list = new PartListenerList();
   
   /**
    * Internal management of {@link IPartListener2}.
    */
   private PartListenerList2 list2 = new PartListenerList2();

   /**
    * Implementation of {@link IPartListener} to detect events
    * and to throw them to listeners contained in {@link #list} in modified form.
    */
   private IPartListener partListener = new IPartListener() {
      @Override
      public void partOpened(IWorkbenchPart part) {
         handlePartOpened(part);
      }
      
      @Override
      public void partDeactivated(IWorkbenchPart part) {
         handlePartDeactivated(part);
      }
      
      @Override
      public void partClosed(IWorkbenchPart part) {
         handlePartClosed(part);
      }
      
      @Override
      public void partBroughtToTop(IWorkbenchPart part) {
         handlePartBroughtToTop(part);
      }
      
      @Override
      public void partActivated(IWorkbenchPart part) {
         handlePartActivated(part);
      }
   };
   
   /**
    * Implementation of {@link IPartListener2} to detect events
    * and to throw them to listeners contained in {@link #list2} in modified form.
    */
   private IPartListener2 partListener2 = new IPartListener2() {
      @Override
      public void partVisible(IWorkbenchPartReference partRef) {
         handlePartVisible(partRef);
      }
      
      @Override
      public void partOpened(IWorkbenchPartReference partRef) {
         handlePartOpened(partRef);
      }
      
      @Override
      public void partInputChanged(IWorkbenchPartReference partRef) {
         handlePartInputChanged(partRef);
      }
      
      @Override
      public void partHidden(IWorkbenchPartReference partRef) {
         handlePartHidden(partRef);
      }
      
      @Override
      public void partDeactivated(IWorkbenchPartReference partRef) {
         handlePartDeactivated(partRef);
      }
      
      @Override
      public void partClosed(IWorkbenchPartReference partRef) {
         handlePartClosed(partRef);
      }
      
      @Override
      public void partBroughtToTop(IWorkbenchPartReference partRef) {
         handlePartBroughtToTop(partRef);
      }
      
      @Override
      public void partActivated(IWorkbenchPartReference partRef) {
         handlePartActivated(partRef);
      }
   };
   
   /**
    * Constructor.
    * @param wrapperViewSite The {@link IViewSite} of an {@link IViewPart} which contains an {@link IEditorPart}.
    * @param wrappedEditorPart The {@link IEditorPart} which is shown in the {@link IViewPart} of {@link #wrapperViewSite}.
    */
   public EditorInViewWorkbenchPage(IViewSite wrapperViewSite,
                                    IEditorPart wrappedEditorPart) {
      super();
      Assert.isNotNull(wrapperViewSite);
      Assert.isNotNull(wrappedEditorPart);
      this.wrapperViewSite = wrapperViewSite;
      this.wrappedEditorPart = wrappedEditorPart;
      this.wrapperViewSite.getPage().addPartListener(partListener);
      this.wrapperViewSite.getPage().addPartListener(partListener2);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Returns the active editor. If the {@link IViewPart} which contains
    * the {@link IEditorPart} is active this method returns the {@link IEditorPart}
    * reference.
    * </p>
    */
   @Override
   public IEditorPart getActiveEditor() {
      IWorkbenchPart activePart = wrapperViewSite.getPage().getActivePart();
      if (activePart != null && ObjectUtil.equals(activePart.getSite(), wrapperViewSite)) {
         return wrappedEditorPart;
      }
      else {
         return wrapperViewSite.getPage().getActiveEditor();
      }
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * Returns also {@code true} for the {@link IEditorPart} if the {@link IViewPart} 
    * which contains it is visible.
    * </p>
    */   
   @Override
   public boolean isPartVisible(IWorkbenchPart part) {
      if (ObjectUtil.equals(part, wrappedEditorPart)) {
         return wrapperViewSite.getPage().isPartVisible(wrapperViewSite.getPart());
      }
      else {
         return wrapperViewSite.getPage().isPartVisible(part);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPartListener(IPartListener listener) {
      list.addPartListener(listener);
   }

   /**
    * Handles the event {@link IPartListener#partActivated(IWorkbenchPart)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param part The {@link IWorkbenchPart} which has caused the event.
    */
   protected void handlePartActivated(IWorkbenchPart part) {
      if (ObjectUtil.equals(part, wrapperViewSite.getPart())) {
         list.firePartActivated(wrappedEditorPart);
      }
      else {
         list.firePartActivated(part);
      }
   }

   /**
    * Handles the event {@link IPartListener#partBroughtToTop(IWorkbenchPart)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param part The {@link IWorkbenchPart} which has caused the event.
    */
   protected void handlePartBroughtToTop(IWorkbenchPart part) {
      if (ObjectUtil.equals(part, wrapperViewSite.getPart())) {
         list.firePartBroughtToTop(wrappedEditorPart);
      }
      else {
         list.firePartBroughtToTop(part);
      }         
   }

   /**
    * Handles the event {@link IPartListener#partClosed(IWorkbenchPart)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param part The {@link IWorkbenchPart} which has caused the event.
    */
   protected void handlePartClosed(IWorkbenchPart part) {
      if (ObjectUtil.equals(part, wrapperViewSite.getPart())) {
         list.firePartClosed(wrappedEditorPart);
      }
      else {
         list.firePartClosed(part);
      }
   }

   /**
    * Handles the event {@link IPartListener#partDeactivated(IWorkbenchPart)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param part The {@link IWorkbenchPart} which has caused the event.
    */
   protected void handlePartDeactivated(IWorkbenchPart part) {
      if (ObjectUtil.equals(part, wrapperViewSite.getPart())) {
         list.firePartDeactivated(wrappedEditorPart);
      }
      else {
         list.firePartDeactivated(part);
      }
   }

   /**
    * Handles the event {@link IPartListener#partOpened(IWorkbenchPart)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param part The {@link IWorkbenchPart} which has caused the event.
    */
   protected void handlePartOpened(IWorkbenchPart part) {
      if (ObjectUtil.equals(part, wrapperViewSite.getPart())) {
         list.firePartOpened(wrappedEditorPart);
      }
      else {
         list.firePartOpened(part);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removePartListener(IPartListener listener) {
      list.removePartListener(listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void addPartListener(IPartListener2 listener) {
      list2.addPartListener(listener);
   }
   
   /**
    * Handles the event {@link IPartListener2#partVisible(IWorkbenchPartReference)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param partRef The {@link IWorkbenchPartReference} which has caused the event.
    */
   protected void handlePartVisible(IWorkbenchPartReference partRef) {
      IWorkbenchPartReference editorRef = wrapperViewSite.getPage().getReference(wrapperViewSite.getPart());
      if (ObjectUtil.equals(partRef, editorRef)) {
         list2.firePartVisible(editorRef);
      }
      else {
         list2.firePartVisible(partRef);
      }
   }

   /**
    * Handles the event {@link IPartListener2#partOpened(IWorkbenchPartReference)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param partRef The {@link IWorkbenchPartReference} which has caused the event.
    */
   protected void handlePartOpened(IWorkbenchPartReference partRef) {
      IWorkbenchPartReference editorRef = wrapperViewSite.getPage().getReference(wrapperViewSite.getPart());
      if (ObjectUtil.equals(partRef, editorRef)) {
         list2.firePartOpened(editorRef);
      }
      else {
         list2.firePartOpened(partRef);
      }
   }

   /**
    * Handles the event {@link IPartListener2#partInputChanged(IWorkbenchPartReference)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param partRef The {@link IWorkbenchPartReference} which has caused the event.
    */
   protected void handlePartInputChanged(IWorkbenchPartReference partRef) {
      IWorkbenchPartReference editorRef = wrapperViewSite.getPage().getReference(wrapperViewSite.getPart());
      if (ObjectUtil.equals(partRef, editorRef)) {
         list2.firePartInputChanged(editorRef);
      }
      else {
         list2.firePartInputChanged(partRef);
      }
   }

   /**
    * Handles the event {@link IPartListener2#partHidden(IWorkbenchPartReference)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param partRef The {@link IWorkbenchPartReference} which has caused the event.
    */
   protected void handlePartHidden(IWorkbenchPartReference partRef) {
      IWorkbenchPartReference editorRef = wrapperViewSite.getPage().getReference(wrapperViewSite.getPart());
      if (ObjectUtil.equals(partRef, editorRef)) {
         list2.firePartHidden(editorRef);
      }
      else {
         list2.firePartHidden(partRef);
      }
   }

   /**
    * Handles the event {@link IPartListener2#partDeactivated(IWorkbenchPartReference)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param partRef The {@link IWorkbenchPartReference} which has caused the event.
    */
   protected void handlePartDeactivated(IWorkbenchPartReference partRef) {
      IWorkbenchPartReference editorRef = wrapperViewSite.getPage().getReference(wrapperViewSite.getPart());
      if (ObjectUtil.equals(partRef, editorRef)) {
         list2.firePartDeactivated(editorRef);
      }
      else {
         list2.firePartDeactivated(partRef);
      }
   }

   /**
    * Handles the event {@link IPartListener2#partClosed(IWorkbenchPartReference)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param partRef The {@link IWorkbenchPartReference} which has caused the event.
    */
   protected void handlePartClosed(IWorkbenchPartReference partRef) {
      IWorkbenchPartReference editorRef = wrapperViewSite.getPage().getReference(wrapperViewSite.getPart());
      if (ObjectUtil.equals(partRef, editorRef)) {
         list2.firePartClosed(editorRef);
      }
      else {
         list2.firePartClosed(partRef);
      }
   }

   /**
    * Handles the event {@link IPartListener2#partBroughtToTop(IWorkbenchPartReference)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param partRef The {@link IWorkbenchPartReference} which has caused the event.
    */
   protected void handlePartBroughtToTop(IWorkbenchPartReference partRef) {
      IWorkbenchPartReference editorRef = wrapperViewSite.getPage().getReference(wrapperViewSite.getPart());
      if (ObjectUtil.equals(partRef, editorRef)) {
         list2.firePartBroughtToTop(editorRef);
      }
      else {
         list2.firePartBroughtToTop(partRef);
      }
   }

   /**
    * Handles the event {@link IPartListener2#partActivated(IWorkbenchPartReference)}
    * by throwing the event to contained listeners. If the {@link IViewPart}
    * has caused the event his contained {@link IEditorPart} is used
    * as event source.
    * @param partRef The {@link IWorkbenchPartReference} which has caused the event.
    */
   protected void handlePartActivated(IWorkbenchPartReference partRef) {
      IWorkbenchPartReference editorRef = wrapperViewSite.getPage().getReference(wrapperViewSite.getPart());
      if (ObjectUtil.equals(partRef, editorRef)) {
         list2.firePartActivated(editorRef);
      }
      else {
         list2.firePartActivated(partRef);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void removePartListener(IPartListener2 listener) {
      list2.removePartListener(listener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      this.wrapperViewSite.getPage().removePartListener(partListener);
      this.wrapperViewSite.getPage().removePartListener(partListener2);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IWorkbenchPart getActivePart() {
      return wrapperViewSite.getPage().getActivePart();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IWorkbenchPartReference getActivePartReference() {
      return wrapperViewSite.getPage().getActivePartReference();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void addSelectionListener(ISelectionListener listener) {
      wrapperViewSite.getPage().addSelectionListener(listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void addSelectionListener(String partId, ISelectionListener listener) {
      wrapperViewSite.getPage().addSelectionListener(partId, listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void addPostSelectionListener(ISelectionListener listener) {
      wrapperViewSite.getPage().addPostSelectionListener(listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void addPostSelectionListener(String partId, ISelectionListener listener) {
      wrapperViewSite.getPage().addPostSelectionListener(partId, listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public ISelection getSelection() {
      return wrapperViewSite.getPage().getSelection();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public ISelection getSelection(String partId) {
      return wrapperViewSite.getPage().getSelection(partId);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void removeSelectionListener(ISelectionListener listener) {
      wrapperViewSite.getPage().removeSelectionListener(listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void removeSelectionListener(String partId, ISelectionListener listener) {
      wrapperViewSite.getPage().removeSelectionListener(partId, listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void removePostSelectionListener(ISelectionListener listener) {
      wrapperViewSite.getPage().removePostSelectionListener(listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void removePostSelectionListener(String partId, ISelectionListener listener) {
      wrapperViewSite.getPage().removePostSelectionListener(partId, listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void activate(IWorkbenchPart part) {
      wrapperViewSite.getPage().activate(part);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @SuppressWarnings("deprecation")
   @Override
   public void addPropertyChangeListener(IPropertyChangeListener listener) {
      wrapperViewSite.getPage().addPropertyChangeListener(listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void bringToTop(IWorkbenchPart part) {
      wrapperViewSite.getPage().bringToTop(part);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public boolean close() {
      return wrapperViewSite.getPage().close();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public boolean closeAllEditors(boolean save) {
      return wrapperViewSite.getPage().closeAllEditors(save);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public boolean closeEditors(IEditorReference[] editorRefs, boolean save) {
      return wrapperViewSite.getPage().closeEditors(editorRefs, save);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public boolean closeEditor(IEditorPart editor, boolean save) {
      return wrapperViewSite.getPage().closeEditor(editor, save);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IViewPart findView(String viewId) {
      return wrapperViewSite.getPage().findView(viewId);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IViewReference findViewReference(String viewId) {
      return wrapperViewSite.getPage().findViewReference(viewId);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IViewReference findViewReference(String viewId, String secondaryId) {
      return wrapperViewSite.getPage().findViewReference(viewId, secondaryId);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IEditorPart findEditor(IEditorInput input) {
      return wrapperViewSite.getPage().findEditor(input);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IEditorReference[] findEditors(IEditorInput input, String editorId, int matchFlags) {
      return wrapperViewSite.getPage().findEditors(input, editorId, matchFlags);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @SuppressWarnings("deprecation")
   @Override
   public IEditorPart[] getEditors() {
      return wrapperViewSite.getPage().getEditors();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IEditorReference[] getEditorReferences() {
      return wrapperViewSite.getPage().getEditorReferences();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IEditorPart[] getDirtyEditors() {
      return wrapperViewSite.getPage().getDirtyEditors();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IAdaptable getInput() {
      return wrapperViewSite.getPage().getInput();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public String getLabel() {
      return wrapperViewSite.getPage().getLabel();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IPerspectiveDescriptor getPerspective() {
      return wrapperViewSite.getPage().getPerspective();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IViewReference[] getViewReferences() {
      return wrapperViewSite.getPage().getViewReferences();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @SuppressWarnings("deprecation")
   @Override
   public IViewPart[] getViews() {
      return wrapperViewSite.getPage().getViews();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IWorkbenchWindow getWorkbenchWindow() {
      return wrapperViewSite.getPage().getWorkbenchWindow();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @SuppressWarnings("deprecation")
   @Override
   public IWorkingSet getWorkingSet() {
      return wrapperViewSite.getPage().getWorkingSet();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void hideActionSet(String actionSetID) {
      wrapperViewSite.getPage().hideActionSet(actionSetID);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void hideView(IViewPart view) {
      wrapperViewSite.getPage().hideView(view);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void hideView(IViewReference view) {
      wrapperViewSite.getPage().hideView(view);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public boolean isEditorAreaVisible() {
      return wrapperViewSite.getPage().isEditorAreaVisible();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void reuseEditor(IReusableEditor editor, IEditorInput input) {
      wrapperViewSite.getPage().reuseEditor(editor, input);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IEditorPart openEditor(IEditorInput input, String editorId) throws PartInitException {
      return wrapperViewSite.getPage().openEditor(input, editorId);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IEditorPart openEditor(IEditorInput input, String editorId, boolean activate) throws PartInitException {
      return wrapperViewSite.getPage().openEditor(input, editorId, activate);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IEditorPart openEditor(IEditorInput input, String editorId, boolean activate, int matchFlags) throws PartInitException {
      return wrapperViewSite.getPage().openEditor(input, editorId, activate, matchFlags);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void removePropertyChangeListener(IPropertyChangeListener listener) {
      wrapperViewSite.getPage().removePropertyChangeListener(listener);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void resetPerspective() {
      wrapperViewSite.getPage().resetPerspective();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public boolean saveAllEditors(boolean confirm) {
      return wrapperViewSite.getPage().saveAllEditors(confirm);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public boolean saveEditor(IEditorPart editor, boolean confirm) {
      return wrapperViewSite.getPage().saveEditor(editor, confirm);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void savePerspective() {
      wrapperViewSite.getPage().savePerspective();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void savePerspectiveAs(IPerspectiveDescriptor perspective) {
      wrapperViewSite.getPage().savePerspectiveAs(perspective);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void setEditorAreaVisible(boolean showEditorArea) {
      wrapperViewSite.getPage().setEditorAreaVisible(showEditorArea);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void setPerspective(IPerspectiveDescriptor perspective) {
      wrapperViewSite.getPage().setPerspective(perspective);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void showActionSet(String actionSetID) {
      wrapperViewSite.getPage().showActionSet(actionSetID);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IViewPart showView(String viewId) throws PartInitException {
      return wrapperViewSite.getPage().showView(viewId);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IViewPart showView(String viewId, String secondaryId, int mode) throws PartInitException {
      return wrapperViewSite.getPage().showView(viewId, secondaryId, mode);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public boolean isEditorPinned(IEditorPart editor) {
      return wrapperViewSite.getPage().isEditorPinned(editor);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @SuppressWarnings("deprecation")
   @Override
   public int getEditorReuseThreshold() {
      return wrapperViewSite.getPage().getEditorReuseThreshold();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @SuppressWarnings("deprecation")
   @Override
   public void setEditorReuseThreshold(int openEditors) {
      wrapperViewSite.getPage().setEditorReuseThreshold(openEditors);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public INavigationHistory getNavigationHistory() {
      return wrapperViewSite.getPage().getNavigationHistory();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IViewPart[] getViewStack(IViewPart part) {
      return wrapperViewSite.getPage().getViewStack(part);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public String[] getNewWizardShortcuts() {
      return wrapperViewSite.getPage().getNewWizardShortcuts();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public String[] getPerspectiveShortcuts() {
      return wrapperViewSite.getPage().getPerspectiveShortcuts();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public String[] getShowViewShortcuts() {
      return wrapperViewSite.getPage().getShowViewShortcuts();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IPerspectiveDescriptor[] getOpenPerspectives() {
      return wrapperViewSite.getPage().getOpenPerspectives();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IPerspectiveDescriptor[] getSortedPerspectives() {
      return wrapperViewSite.getPage().getSortedPerspectives();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void closePerspective(IPerspectiveDescriptor desc, boolean saveParts, boolean closePage) {
      wrapperViewSite.getPage().closePerspective(desc, saveParts, closePage);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void closeAllPerspectives(boolean saveEditors, boolean closePage) {
      wrapperViewSite.getPage().closeAllPerspectives(saveEditors, closePage);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IExtensionTracker getExtensionTracker() {
      return wrapperViewSite.getPage().getExtensionTracker();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IWorkingSet[] getWorkingSets() {
      return wrapperViewSite.getPage().getWorkingSets();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void setWorkingSets(IWorkingSet[] sets) {
      wrapperViewSite.getPage().setWorkingSets(sets);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IWorkingSet getAggregateWorkingSet() {
      return wrapperViewSite.getPage().getAggregateWorkingSet();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public boolean isPageZoomed() {
      return wrapperViewSite.getPage().isPageZoomed();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void zoomOut() {
      wrapperViewSite.getPage().zoomOut();
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void toggleZoom(IWorkbenchPartReference ref) {
      wrapperViewSite.getPage().toggleZoom(ref);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public int getPartState(IWorkbenchPartReference ref) {
      return wrapperViewSite.getPage().getPartState(ref);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void setPartState(IWorkbenchPartReference ref, int state) {
      wrapperViewSite.getPage().setPartState(ref, state);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IWorkbenchPartReference getReference(IWorkbenchPart part) {
      return wrapperViewSite.getPage().getReference(part);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void showEditor(IEditorReference ref) {
      wrapperViewSite.getPage().showEditor(ref);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public void hideEditor(IEditorReference ref) {
      wrapperViewSite.getPage().hideEditor(ref);
   }

   /**
    * <p>
    * {@inheritDoc}
    * </p>
    * <p>
    * The call is delegated to the {@link IViewSite}.
    * </p>
    */
   @Override
   public IEditorReference[] openEditors(IEditorInput[] inputs, String[] editorIDs, int matchFlags) throws MultiPartInitException {
      return wrapperViewSite.getPage().openEditors(inputs, editorIDs, matchFlags);
   }
}