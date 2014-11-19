package org.key_project.jmlediting.ui.extension;

import org.eclipse.jdt.internal.ui.text.JavaPresentationReconciler;
import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.presentation.IPresentationDamager;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.IPresentationRepairer;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.graphics.*;

public class JMLPresentationReconciler extends JavaPresentationReconciler {
   
   private IPresentationReconciler javaPR;
   /**
    * Creates an Instance of JMLPresentationReconciler which is the standard
    * JavaPresentationReconciler with added Damagers and Repairers for
    * JML ContentTypes 
    */
   public JMLPresentationReconciler(IPresentationReconciler currentResult) {
      super();
      //this.javaPR=javaPR;
      
   }
}
