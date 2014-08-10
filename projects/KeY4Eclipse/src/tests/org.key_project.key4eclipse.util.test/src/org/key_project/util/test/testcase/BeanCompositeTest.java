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

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Shell;
import org.key_project.util.eclipse.swt.BeanComposite;

/**
 * Tests for {@link BeanComposite}.
 * @author Martin Hentschel
 */
public class BeanCompositeTest extends AbstractIBeanTest {
   /**
    * {@inheritDoc}
    */
   @Override
   protected ITestBean createTestBean() {
      return new TestBeanViewPart();
   }
   
   /**
    * The used example bean.
    * @author Martin Hentschel
    */
   private static class TestBeanViewPart extends BeanComposite implements ITestBean {
      /**
       * An object value.
       */
      private Object objectValue;
      
      /**
       * An int value.
       */
      private int intValue;
      
      /**
       * An boolean value.
       */
      private boolean booleanValue;
      
      /**
       * An object array.
       */
      private Object[] objectArray = new Object[2];
      
      /**
       * An int array.
       */
      private int[] intArray = new int[2];
      
      /**
       * An boolean array.
       */
      private boolean[] booleanArray = new boolean[2];       
      
      /**
       * Constructor.
       */
      public TestBeanViewPart() {
         super(new Shell(), SWT.NONE);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object getObjectValue() {
         return objectValue;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void setObjectValue(Object objectValue) {
         Object oldValue = getObjectValue();
         this.objectValue = objectValue;
         firePropertyChange(PROP_OBJECT_VALUE, oldValue, getObjectValue());
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int getIntValue() {
         return intValue;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void setIntValue(int intValue) {
         int oldValue = getIntValue();
         this.intValue = intValue;
         firePropertyChange(PROP_INT_VALUE, oldValue, getIntValue());
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean isBooleanValue() {
         return booleanValue;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void setBooleanValue(boolean booleanValue) {
         boolean oldValue = isBooleanValue();
         this.booleanValue = booleanValue;
         firePropertyChange(PROP_BOOLEAN_VALUE, oldValue, isBooleanValue());
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object getObjectArray(int index) {
         return objectArray[index];
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void setObjectArray(int index, Object objectValue) {
         Object oldValue = getObjectArray(index);
         this.objectArray[index] = objectValue;
         fireIndexedPropertyChange(PROP_OBJECT_ARRAY, index, oldValue, getObjectArray(index));
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public int getIntArray(int index) {
         return intArray[index];
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void setIntArray(int index, int intValue) {
         int oldValue = getIntArray(index);
         this.intArray[index] = intValue;
         fireIndexedPropertyChange(PROP_INT_ARRAY, index, oldValue, getIntArray(index));
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public boolean getBooleanArray(int index) {
         return booleanArray[index];
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void setBooleanArray(int index, boolean booleanValue) {
         boolean oldValue = getBooleanArray(index);
         this.booleanArray[index] = booleanValue;
         fireIndexedPropertyChange(PROP_BOOLEAN_ARRAY, index, oldValue, getBooleanArray(index));
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public void fireInvalidEvent() {
         firePropertyChange(new PropertyChangeEvent(this, "INVALID", "INVALID_OLD", "INVALID_NEW"));
      }
   }
}