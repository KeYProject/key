package org.key_project.keyide.ui.providers;


import org.eclipse.jface.viewers.LabelProvider;
import org.eclipse.swt.graphics.Image;
import org.key_project.keyide.ui.util.KeYImages;
import org.key_project.util.java.ObjectUtil;

import de.uka.ilkd.key.proof.Goal;


/**
 * The {@link LabelProvider} to label the list of open {@link Goal}s on
 * the GoalsView
 * 
 * @author Seena Vellaramkalayil
 *
 */
public class GoalsLabelProvider extends LabelProvider {

   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getText(Object element) {
      if (element instanceof Goal) {
         Goal goal = (Goal) element;
         return getString(goal);
      }
      
      return ObjectUtil.toString(element);
   }
   
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Image getImage(Object element) {
      if (element instanceof Goal) {
         return KeYImages.getImage(KeYImages.NODE);
      }
      return super.getImage(element);
   }
   
   /**
    * static method to get the text to displayin the viewer.
    * @param goal the {@link Goal} to be displayed
    * @return the text to be displayed
    */
   public static String getString(Goal goal) {
      return "(#" + goal.node().serialNr() + ") " + goal.toString();
   }

}
