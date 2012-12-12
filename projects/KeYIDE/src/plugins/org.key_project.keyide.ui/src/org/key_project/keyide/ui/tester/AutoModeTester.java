package org.key_project.keyide.ui.tester;

import org.eclipse.core.expressions.PropertyTester;
import org.key_project.keyide.ui.editor.KeYEditor;

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
         ConsoleUserInterface userInterface = (ConsoleUserInterface)editor.getKeYEnvironment().getUi();
         //Set button states
         if("start".equals(property)){
            return  !userInterface.isAutoMode();
         }
         if("stop".equals(property)){
            return userInterface.isAutoMode();
         }
      }
      return false;
   }
}

