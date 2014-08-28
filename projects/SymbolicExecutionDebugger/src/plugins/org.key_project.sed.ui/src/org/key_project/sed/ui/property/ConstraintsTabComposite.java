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
import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IVariable;
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
    * Optionally the currently shown value.
    */
   private ISEDValue value;
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createComposite(Composite parent, TabbedPropertySheetWidgetFactory factory) {
      this.parent = parent;
      this.relevantColor = new Color(parent.getDisplay(), 200, 0, 0); // red
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateContent(IVariable variable) {
      value = null;
      if (variable instanceof ISEDVariable) {
         IStackFrame frame = ((ISEDVariable) variable).getStackFrame();
         if (frame instanceof ISEDDebugNode) {
            try {
               if (variable.getValue() instanceof ISEDValue) {
                  value = (ISEDValue) variable.getValue();
               }
            }
            catch (DebugException e) {
               // Nothing to do.
            }
            doUpdateContent((ISEDDebugNode) frame);
         }
         else {
            doUpdateContent((ISEDDebugNode)null);
         }
      }
      else {
         doUpdateContent((ISEDDebugNode)null);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void updateContent(ISEDDebugNode node) {
      value = null;
      doUpdateContent(node);
   }

   /**
    * Updates the shown content.
    * @param node The {@link ISEDDebugNode} which provides the content to show.
    */
   protected void doUpdateContent(ISEDDebugNode node) {
      try {
         if (viewer != null) {
            viewer.getTable().dispose();
         }
         viewer = new TableViewer(parent, SWT.MULTI);
         viewer.getTable().setLinesVisible(true);
         viewer.setContentProvider(ArrayContentProvider.getInstance());
         viewer.setLabelProvider(new AbstractMultiLineLabelProvider() {
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
               try {
                  if (value != null && element instanceof ISEDConstraint) {
                     if (ArrayUtil.contains(value.getRelevantConstraints(), (ISEDConstraint) element)) {
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
               catch (DebugException e) {
                  return null;
               }
            }
         });
         parent.layout();
         if (node != null && node.hasConstraints()) {
            viewer.setInput(node.getConstraints());
         }
         else {
            viewer.setInput(new Object[0]);
         }
      }
      catch (DebugException e) {
         LogUtil.getLogger().logError(e);
         viewer.setInput(new Object[0]);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      if (relevantColor != null) {
         relevantColor.dispose();
      }
   }
}