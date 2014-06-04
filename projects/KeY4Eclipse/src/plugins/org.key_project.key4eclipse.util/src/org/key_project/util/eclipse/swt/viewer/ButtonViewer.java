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

package org.key_project.util.eclipse.swt.viewer;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.Assert;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredViewer;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Widget;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;

/**
 * A {@link StructuredViewer} which allows to select one or multiple values
 * via radio/checkbox buttons.
 * @author Martin Hentschel
 */
public class ButtonViewer extends StructuredViewer {
   /**
    * The button style to use. E.g. {@link SWT#RADIO} or {@link SWT#CHECK}.
    */
   private int buttonStyle;
   
   /**
    * The root {@link Composite} of this {@link StructuredViewer}.
    */
   private Composite root;
   
   /**
    * The currently shown {@link Button}s.
    */
   private List<Button> buttons = new LinkedList<Button>();
   
   /**
    * Listens for changes on each {@link Button} provided by {@link #buttons}.
    */
   private SelectionListener buttonListener = new SelectionAdapter() {
      @Override
      public void widgetSelected(SelectionEvent e) {
         handleWidgetSelected(e);
      }
   };
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param buttonStyle The button style to use. E.g. {@link SWT#RADIO} or {@link SWT#CHECK}.
    */
   public ButtonViewer(Composite parent, int buttonStyle) {
      this.buttonStyle = buttonStyle;
      root = new Composite(parent, SWT.NONE);
      root.setLayout(new GridLayout(1, false));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void inputChanged(Object input, Object oldInput) {
      // Remove old elements
      unmapAllElements();
      for (Button button : buttons) {
         button.removeSelectionListener(buttonListener);
         button.setVisible(false);
         button.dispose();
      }
      buttons.clear();
      // Add new elements
      Object[] children = getSortedChildren(getRoot());
      for (Object child : children) {
         Button button = new Button(root, buttonStyle);
         button.setData(child);
         updateButtonText(button, child);
         button.addSelectionListener(buttonListener);
         mapElement(child, button);
         buttons.add(button);
      }
   }
   
   /**
    * Updates the shown text of the given {@link Button}.
    * @param button The {@link Button}.
    * @param element The element shown on the {@link Button}.
    */
   protected void updateButtonText(Button button, Object element) {
      ILabelProvider labelProvider = (ILabelProvider)getLabelProvider();
      Assert.isTrue(getLabelProvider() == null || getLabelProvider() instanceof ILabelProvider, "Label provider must be an instance of ILabelProvider.");
      if (labelProvider != null) {
         SWTUtil.setText(button, labelProvider.getText(element));
      }
      else {
         SWTUtil.setText(button, ObjectUtil.toString(element));
      }
   }
   
   /**
    * When a new {@link Button} of {@link #buttons} was selected.
    * @param e The event.
    */
   protected void handleWidgetSelected(SelectionEvent e) {
      fireSelectionChanged(new SelectionChangedEvent(this, getSelection()));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Widget doFindInputItem(Object element) {
      if (element != null && equals(element, getRoot())) {
         return getControl();
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected Widget doFindItem(final Object element) {
      return CollectionUtil.search(buttons, new IFilter<Button>() {
         @Override
         public boolean select(Button button) {
            return ObjectUtil.equals(button.getData(), element);
         }
      });
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void doUpdateItem(Widget item, Object element, boolean fullMap) {
      if (item instanceof Button) {
         Button button = (Button)item;
         updateButtonText(button, element);
      }
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   protected List getSelectionFromWidget() {
      List<Object> result = new LinkedList<Object>();
      for (Button button : buttons) {
         if (button.getSelection()) {
            result.add(button.getData());
         }
      }
      return result;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void internalRefresh(Object element) {
      Widget widget = findItem(element);
      if (widget instanceof Button) {
         updateButtonText((Button)widget, element);
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void reveal(Object element) {
      Widget widget = findItem(element);
      Assert.isTrue(widget instanceof Button);
      ((Button)widget).setFocus();
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   protected void setSelectionToWidget(List l, boolean reveal) {
      for (Button button : buttons) {
         button.setSelection(l.contains(button.getData()));
      }
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Composite getControl() {
      return root;
   }
}