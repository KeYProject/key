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
   /**
    * the {@link IPresentationReconciler} the JavaEditor is using
    */
   
   /**
    * Creates an Instance of JMLPresentationReconciler
    * @param javaEditorPresentationReconciler the IPresentationReconciler the javaEditor uses
    */
   public JMLPresentationReconciler() {
      super();
      DefaultDamagerRepairer dr= new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(new Color(Display.getCurrent(),new RGB(255,0,0)))));
      this.setDamager(dr,JMLPartitionScanner.JML_SINGLE_LINE);
      this.setDamager(dr, JMLPartitionScanner.JML_MULTI_LINE);
      this.setRepairer(dr, JMLPartitionScanner.JML_SINGLE_LINE);
      this.setRepairer(dr, JMLPartitionScanner.JML_MULTI_LINE);
   }
   
}
