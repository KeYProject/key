package org.key_project.keyide.ui.tester;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.ui.ConsoleUserInterface;

/**
 * A class to test for properties of the {@link KeYEditor} to set the correct GUI states.
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class AutoModeTester extends PropertyTester {
   
   public static final String PROPERTY_NAMESPACE = "org.key_project.keyide.ui.AutoModeTester";
   public static final String PROPERTY_START = "start";
   public static final String PROPERTY_STOP = "stop";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean test(final Object receiver, 
                       final String property, 
                       final Object[] args, 
                       final Object expectedValue) {
      if(receiver instanceof KeYEditor){
         //initialize values
         KeYEditor editor = (KeYEditor) receiver;
         ConsoleUserInterface userInterface = editor.getKeYEnvironment().getUi();
         //Set button states
         if(PROPERTY_START.equals(property)) {
            return !userInterface.isAutoMode();
         }
         if(PROPERTY_STOP.equals(property)) {
            return userInterface.isAutoMode();
         }
      }
      return false;
   }

   /**
    * Re-evaluates all properties defined by this {@link PropertyTester}.
    */
   public static void updateProperties() {
      WorkbenchUtil.updatePropertyTesters(PROPERTY_NAMESPACE + "." + PROPERTY_START, 
                                          PROPERTY_NAMESPACE + "." + PROPERTY_STOP);
   }
}

