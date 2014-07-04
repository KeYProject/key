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

package org.key_project.util.test.testcase;

import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import junit.framework.TestCase;

import org.eclipse.jface.viewers.ArrayContentProvider;
import org.eclipse.jface.viewers.ILabelProvider;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.jface.viewers.LabelProviderChangedEvent;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.swt.SWT;
import org.eclipse.swt.layout.FillLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Control;
import org.eclipse.swt.widgets.Shell;
import org.junit.Test;
import org.key_project.util.bean.Bean;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.eclipse.swt.viewer.ButtonViewer;
import org.key_project.util.java.CollectionUtil;

/**
 * Tests for {@link ButtonViewer}.
 * @author Martin Hentschel
 */
public class ButtonViewerTest extends TestCase {
   /**
    * Tests selection changes.
    */
   public void testSelectionChanges() {
      // Create model
      SimpleBean first = new SimpleBean("First"); 
      SimpleBean second = new SimpleBean("Second"); 
      SimpleBean third = new SimpleBean("Third"); 
      List<SimpleBean> model = CollectionUtil.toList(first, second, third);
      // Create UI
      Shell shell = new Shell();
      shell.setLayout(new FillLayout());
      ButtonViewer viewer = new ButtonViewer(shell, SWT.CHECK);
      LoggingSelectionChangedListener logListener = new LoggingSelectionChangedListener();
      viewer.addSelectionChangedListener(logListener);
      viewer.setContentProvider(ArrayContentProvider.getInstance());
      viewer.setInput(model);
      // Create selections
      ISelection emptySelection = StructuredSelection.EMPTY;
      ISelection secondSelection = SWTUtil.createSelection(second);
      ISelection firstAndThirdSelection = SWTUtil.createSelection(first, third);
      // Test initial selection
      assertEquals(emptySelection, viewer.getSelection());
      logListener.assertAndClearLog();
      // Select one element
      viewer.setSelection(secondSelection);
      assertEquals(secondSelection, viewer.getSelection());
      logListener.assertAndClearLog(new SelectionChangedEvent(viewer, secondSelection));
      // Select two elements
      viewer.setSelection(firstAndThirdSelection);
      assertEquals(firstAndThirdSelection, viewer.getSelection());
      logListener.assertAndClearLog(new SelectionChangedEvent(viewer, firstAndThirdSelection));
      // Test initial selection again
      viewer.setSelection(emptySelection);
      assertEquals(emptySelection, viewer.getSelection());
      logListener.assertAndClearLog(new SelectionChangedEvent(viewer, emptySelection));
      // Select one element again
      viewer.setSelection(secondSelection);
      assertEquals(secondSelection, viewer.getSelection());
      logListener.assertAndClearLog(new SelectionChangedEvent(viewer, secondSelection));
   }
   
   /**
    * A logging {@link ISelectionChangedListener}.
    * @author Martin Hentschel
    */
   private static class LoggingSelectionChangedListener implements ISelectionChangedListener {
      /**
       * The caught events.
       */
      private List<SelectionChangedEvent> eventLog = new LinkedList<SelectionChangedEvent>();

      /**
       * {@inheritDoc}
       */
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         eventLog.add(event);
      }
      
      /**
       * Makes sure that the caught events are equal to the given expected onces.
       * @param expectedEvents The expected events.
       */
      public void assertAndClearLog(SelectionChangedEvent... expectedEvents) {
         assertEquals(expectedEvents.length, eventLog.size());
         for (int i = 0; i < expectedEvents.length; i++) {
            SelectionChangedEvent expected = expectedEvents[i];
            SelectionChangedEvent current = eventLog.get(i);
            assertEquals(expected.getSource(), current.getSource());
            assertEquals(expected.getSelection(), current.getSelection());
            assertEquals(expected.getSelectionProvider(), current.getSelectionProvider());
         }
         eventLog.clear();
      }
   }
   
   /**
    * Tests the shown values using an {@link ILabelProvider}.
    */
   @Test
   public void testShownValues_LabelProvider() {
      SimpleBeanLabelProvider labelProvider = new SimpleBeanLabelProvider();
      try {
         doTestShownValues(labelProvider);
      }
      finally {
         labelProvider.dispose();
      }
   }

   /**
    * Tests the shown values without an {@link ILabelProvider}.
    */
   @Test
   public void testShownValues_NoLabelProvider() {
      doTestShownValues(null);
   }
   
   /**
    * Executes the test steps of {@link #testShownValues_LabelProvider()}
    * and {@link #testShownValues_NoLabelProvider()}.
    * @param labelProvider The {@link ILabelProvider} to use.
    */
   protected void doTestShownValues(ILabelProvider labelProvider) {
      // Create model
      List<SimpleBean> model = new LinkedList<SimpleBean>();
      model.add(new SimpleBean("First"));
      model.add(new SimpleBean("Second"));
      model.add(new SimpleBean("Third"));
      // Create UI
      Shell shell = new Shell();
      shell.setLayout(new FillLayout());
      ButtonViewer viewer = new ButtonViewer(shell, SWT.RADIO);
      viewer.setContentProvider(ArrayContentProvider.getInstance());
      viewer.setLabelProvider(labelProvider);
      viewer.setInput(model);
      // Test initial content
      assertShownContent(viewer, model);
      // Add element
      model.add(new SimpleBean("Fourth"));
      viewer.setInput(model);
      assertShownContent(viewer, model);
      // Remove element
      model.remove(2);
      viewer.setInput(model);
      assertShownContent(viewer, model);
      // Test change element
      if (labelProvider != null) {
         model.get(1).setText(model.get(1).getText() + "-Changed");
         assertShownContent(viewer, model);
      }
   }
   
   /**
    * Makes sure that the shown content is correct.
    * @param viewer The {@link ButtonViewer} to test.
    * @param model The expected values.
    */
   protected void assertShownContent(ButtonViewer viewer, List<SimpleBean> model) {
      Control[] children = viewer.getControl().getChildren();
      assertEquals(model.size(), children.length);
      Iterator<SimpleBean> modelIter = model.iterator();
      for (Control child : children) {
         assertTrue(child instanceof Button);
         SimpleBean bean = modelIter.next();
         assertEquals(bean, child.getData());
         if (viewer.getLabelProvider() != null) {
            assertEquals(((ILabelProvider)viewer.getLabelProvider()).getText(bean), ((Button)child).getText());
         }
         else {
            assertEquals(bean.toString(), ((Button)child).getText());
         }
      }
   }
   
   /**
    * A simple {@link Bean}.
    * @author Martin Hentschel
    */
   private static class SimpleBean extends Bean {
      /**
       * Property {@link #getText()}.
       */
      public static final String PROP_TEXT = "text";
      
      /**
       * A text.
       */
      private String text;

      /**
       * Constructor.
       * @param text A text.
       */
      public SimpleBean(String text) {
         this.text = text;
      }

      /**
       * Returns the text.
       * @return The text.
       */
      public String getText() {
         return text;
      }

      /**
       * Sets the text.
       * @param text The text to set.
       */
      public void setText(String text) {
         String oldValue = getText();
         this.text = text;
         firePropertyChange(PROP_TEXT, oldValue, getText());
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         return text + "#toString()";
      }
   }
   
   /**
    * An {@link ILabelProvider} for {@link SimpleBean}s.
    * @author Martin Hentschel
    */
   private static class SimpleBeanLabelProvider extends LabelProvider {
      /**
       * The known and observed {@link SimpleBean}s.
       */
      private Set<SimpleBean> observedBeans = new HashSet<SimpleBean>();
      
      /**
       * Listens for changes of {@link SimpleBean#getText()}.
       */
      private PropertyChangeListener changeListener = new PropertyChangeListener() {
         @Override
         public void propertyChange(PropertyChangeEvent evt) {
            fireLabelProviderChanged(new LabelProviderChangedEvent(SimpleBeanLabelProvider.this, evt.getSource()));
         }
      };
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String getText(Object element) {
         if (element instanceof SimpleBean) {
            SimpleBean bean = (SimpleBean) element;
            if (!observedBeans.contains(bean)) {
               observedBeans.add(bean);
               bean.addPropertyChangeListener(SimpleBean.PROP_TEXT, changeListener);
            }
            return bean.getText();
         }
         else {
            return null;
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void dispose() {
         for (SimpleBean bean : observedBeans) {
            bean.removePropertyChangeListener(SimpleBean.PROP_TEXT, changeListener);
         }
         observedBeans.clear();
         super.dispose();
      }
   }
}