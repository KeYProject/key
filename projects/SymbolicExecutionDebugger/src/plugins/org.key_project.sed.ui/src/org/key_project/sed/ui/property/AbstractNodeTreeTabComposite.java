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

package org.key_project.sed.ui.property;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.internal.ui.viewers.model.provisional.PresentationContext;
import org.eclipse.debug.internal.ui.viewers.model.provisional.TreeModelViewer;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jface.viewers.DoubleClickEvent;
import org.eclipse.jface.viewers.IDoubleClickListener;
import org.eclipse.jface.viewers.TreeViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.layout.FormAttachment;
import org.eclipse.swt.layout.FormData;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Group;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.views.properties.tabbed.ITabbedPropertyConstants;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDUIUtil;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * This composite provides the functionality to show {@link ISEDDebugNode}s
 * in a {@link TreeViewer}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public abstract class AbstractNodeTreeTabComposite implements ISEDDebugNodeTabContent {
   /**
    * Shows the name of the current node.
    */
   private Group viewerGroup;
   
   /**
    * Shows the call stack {@link ISEDDebugNode#getCallStack()}.
    */
   private TreeModelViewer viewer;
   
   /**
    * The used {@link PresentationContext} in {@link #viewer}.
    */
   private PresentationContext viewerContext;
   
   /**
    * Constructor.
    */
   public AbstractNodeTreeTabComposite() {
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createComposite(Composite parent, TabbedPropertySheetWidgetFactory factory) {
      Composite composite = factory.createFlatFormComposite(parent);
      
      viewerGroup = factory.createGroup(composite, getGroupName());
      viewerGroup.setLayout(new FillLayout());
      FormData data = new FormData();
      data.left = new FormAttachment(0, 0);
      data.right = new FormAttachment(100, 0);
      data.top = new FormAttachment(0, ITabbedPropertyConstants.VSPACE);
      viewerGroup.setLayoutData(data);
      
      viewerContext = createPresentationContext();
      viewer = new TreeModelViewer(viewerGroup, SWT.MULTI | SWT.H_SCROLL | SWT.V_SCROLL | SWT.VIRTUAL, viewerContext);
      viewer.addDoubleClickListener(new IDoubleClickListener() {
         @Override
         public void doubleClick(DoubleClickEvent event) {
            handleDoubleClick(event);
         }
      });
   }
   
   /**
    * Returns the text to show in the group.
    * @return The text to show.
    */
   protected abstract String getGroupName();
   
   /**
    * Creates the {@link PresentationContext} to use.
    * @return The {@link PresentationContext} to use.
    */
   protected abstract PresentationContext createPresentationContext();

   /**
    * When a double click on an stack entry was done.
    * @param event The event.
    */
   protected void handleDoubleClick(DoubleClickEvent event) {
      IViewPart debugView = WorkbenchUtil.findView(IDebugUIConstants.ID_DEBUG_VIEW);
      if (debugView instanceof IDebugView) {
         SEDUIUtil.selectInDebugView(WorkbenchUtil.getActivePart(), (IDebugView)debugView, viewer.getSelection());
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateContent(ISEDDebugNode node) {
      String nodeText = getGroupName();
      try {
         if (node != null) {
            nodeText = getGroupName() + " of: " + node.getName();
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
      }
      configurePresentationContext(viewerContext, node);
      viewer.setInput(node);
      viewerGroup.setText(nodeText);
   }
   
   /**
    * Configures the {@link PresentationContext} before the input of the {@link TreeViewer} is updated.
    * @param viewerContext The {@link PresentationContext} to modify.
    * @param node The {@link ISEDDebugNode} to set as {@link TreeViewer} input.
    */
   protected abstract void configurePresentationContext(PresentationContext viewerContext, ISEDDebugNode node);

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
   }
}