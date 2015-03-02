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

import java.util.LinkedHashSet;
import java.util.Set;

import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.jface.action.Action;
import org.eclipse.jface.action.MenuManager;
import org.eclipse.jface.util.IPropertyChangeListener;
import org.eclipse.jface.util.PropertyChangeEvent;
import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.TableViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.graphics.Color;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.properties.tabbed.TabbedPropertySheetWidgetFactory;
import org.key_project.sed.core.model.ISEDConstraint;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDValue;
import org.key_project.sed.core.model.ISEDVariable;
import org.key_project.sed.ui.util.LogUtil;
import org.key_project.sed.ui.util.SEDImages;
import org.key_project.sed.ui.util.SEDUIPreferenceUtil;
import org.key_project.util.eclipse.swt.viewer.AbstractMultiLineLabelProvider;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.ObjectUtil;

/**
 * This composite provides the content shown in {@link ConstraintsNodePropertySection}
 * and in {@code GraphitiCallStackPropertySection} as well as in
 * {@link ConstraintsVariablePropertySection}.
 * @author Martin Hentschel
 */
public class ConstraintsTabComposite implements ISEDDebugNodeTabContent, IVariableTabContent {
   /**
    * The {@link Color} used to highlight relevant constraints.
    */
   private Color relevantColor;
   
   /**
    * The parent {@link Composite}.
    */
   private Composite parent;
   
   /**
    * The {@link TableViewer} which shows the constraints.
    */
   private TableViewer viewer;
   
   /**
    * The used {@link AbstractMultiLineLabelProvider}.
    */
   private final AbstractMultiLineLabelProvider labelProvider = new AbstractMultiLineLabelProvider() {
      @Override
      protected String getText(Object element) {
         try {
            if (element instanceof ISEDConstraint) {
               return ((ISEDConstraint) element).getName();
            }
            else {
               return ObjectUtil.toString(element);
            }
         }
         catch (DebugException e) {
            LogUtil.getLogger().logError(e);
            return e.getMessage();
         }
      }

      @Override
      protected Color getForeground(Object element) {
         if (SEDUIPreferenceUtil.isShowAllConstraints()) {
            if (relevantConstraints != null && relevantConstraints.contains(element)) {
               return relevantColor;
            }
            else {
               return null;
            }
         }
         else {
            return null;
         }
      }
   };
   
   /**
    * The {@link Action} used to toggle between all and only relevant shown constraints.
    */
   private final Action showAllConstraintsAction = new Action("&Show all constraints", SEDImages.getImageDescriptor(SEDImages.SHOW_ALL_CONSTRAINTS)) {
      @Override
      public void run() {
         toggleShownContent();
      }
   };

   /**
    * Listens for changes on {@link SEDUIPreferenceUtil#getStore()}.
    */
   private final IPropertyChangeListener propertyChangeListener = new IPropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent event) {
         handlePropertyChange(event);
      }
   };
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createComposite(Composite parent, TabbedPropertySheetWidgetFactory factory) {
      this.parent = parent;
      this.relevantColor = new Color(parent.getDisplay(), 200, 0, 0); // red
      SEDUIPreferenceUtil.getStore().addPropertyChangeListener(propertyChangeListener);
      showAllConstraintsAction.setChecked(SEDUIPreferenceUtil.isShowAllConstraints());
   }
   
   private ISEDConstraint[] allConstraints;
   
   private Set<ISEDConstraint> relevantConstraints;

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateContent(IVariable variable) {
      if (variable instanceof ISEDVariable) {
         IStackFrame frame = ((ISEDVariable) variable).getStackFrame();
         if (frame instanceof ISEDDebugNode) {
            ISEDValue value = null;
            try {
               if (variable.getValue() instanceof ISEDValue) {
                  value = (ISEDValue) variable.getValue();
               }
            }
            catch (DebugException e) {
               // Nothing to do.
            }
            doUpdateContent((ISEDDebugNode) frame, value);
         }
         else {
            doUpdateContent(null, null);
         }
      }
      else {
         doUpdateContent(null, null);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateContent(ISEDDebugNode node) {
      doUpdateContent(node, null);
   }

   /**
    * Updates the shown content.
    * @param node The {@link ISEDDebugNode} which provides the content to show.
    */
   protected void doUpdateContent(ISEDDebugNode node, ISEDValue value) {
      try {
         allConstraints = node != null && node.hasConstraints() ?
                          node.getConstraints() : 
                          new ISEDConstraint[0];
         if (value != null) {
            relevantConstraints = new LinkedHashSet<ISEDConstraint>();
            ISEDConstraint[] availableRelevantConstraints = value.getRelevantConstraints();
            for (ISEDConstraint constraint : allConstraints) {
               if (ArrayUtil.contains(availableRelevantConstraints, constraint)) {
                  relevantConstraints.add(constraint);
               }
            }
         }
         else {
            relevantConstraints = null;
         }
         recrateViewer();
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         viewer.setInput(new Object[0]);
      }
   }
   
   /**
    * Updates the shown content.
    * @param content The new Content to show.
    */
   protected void recrateViewer() {
      if (viewer != null) {
         viewer.getTable().dispose();
      }
      viewer = new TableViewer(parent, SWT.MULTI);
      viewer.getTable().setLinesVisible(true);
      viewer.setContentProvider(ArrayContentProvider.getInstance());
      viewer.setLabelProvider(labelProvider);
      parent.layout();
      viewer.setInput(relevantConstraints != null && !SEDUIPreferenceUtil.isShowAllConstraints() ? 
                      relevantConstraints : 
                      allConstraints);
      if (relevantConstraints != null) {
         MenuManager menuManager = new MenuManager();
         menuManager.add(showAllConstraintsAction);
         viewer.getTable().setMenu(menuManager.createContextMenu(viewer.getTable()));
      }
   }

   /**
    * Toggles the shown content.
    */
   public void toggleShownContent() {
      SEDUIPreferenceUtil.setShowAllConstraints(!SEDUIPreferenceUtil.isShowAllConstraints());
   }

   /**
    * When a property on {@link SEDUIPreferenceUtil#getStore()} has changed.
    * @param event The event.
    */
   protected void handlePropertyChange(PropertyChangeEvent event) {
      if (SEDUIPreferenceUtil.PROP_SHOW_ALL_CONSTRAINTS.equals(event.getProperty())) {
         showAllConstraintsAction.setChecked(SEDUIPreferenceUtil.isShowAllConstraints());
         if (allConstraints != null) {
            parent.getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  recrateViewer();
               }
            });
         }
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      SEDUIPreferenceUtil.getStore().removePropertyChangeListener(propertyChangeListener);
      if (relevantColor != null) {
         relevantColor.dispose();
      }
      if (labelProvider != null) {
         labelProvider.dispose();
      }
   }
}