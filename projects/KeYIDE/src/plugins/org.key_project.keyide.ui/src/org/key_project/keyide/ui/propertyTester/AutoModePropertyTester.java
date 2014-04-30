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

package org.key_project.keyide.ui.propertyTester;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.ui.ConsoleUserInterface;

/**
 * A class to test for properties of the {@link KeYEditor} to set the correct GUI states.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class AutoModePropertyTester extends PropertyTester {
   /**
    * The namespace of this {@link PropertyTester}.
    */
   public static final String PROPERTY_NAMESPACE = "org.key_project.keyide.ui";
   
   /**
    * The name of the start property.
    */
   public static final String PROPERTY_IS_NOT_AUTO_MODE = "isNotAutoMode";
   
   /**
    * The name of the stop property.
    */
   public static final String PROPERTY_IS_AUTO_MODE = "isAutoMode";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(final Object receiver, 
                       final String property, 
                       final Object[] args, 
                       final Object expectedValue) {
      if (receiver instanceof KeYEditor) {
         KeYEditor editor = (KeYEditor) receiver;
         ConsoleUserInterface userInterface = editor.getUI();
         if (userInterface != null) {
            if (PROPERTY_IS_NOT_AUTO_MODE.equals(property)) {
               return !userInterface.isAutoMode();
            }
            if (PROPERTY_IS_AUTO_MODE.equals(property)) {
               return userInterface.isAutoMode();
            }
         }
         else {
            return false;
         }
      }
      return false;
   }

   /**
    * Re-evaluates all properties defined by this {@link PropertyTester}.
    */
   public static void updateProperties() {
      WorkbenchUtil.updatePropertyTesters(PROPERTY_NAMESPACE + "." + PROPERTY_IS_NOT_AUTO_MODE, 
                                          PROPERTY_NAMESPACE + "." + PROPERTY_IS_AUTO_MODE);
   }
}