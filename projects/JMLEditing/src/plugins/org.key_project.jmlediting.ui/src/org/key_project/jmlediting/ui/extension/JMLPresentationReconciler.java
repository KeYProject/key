package org.key_project.jmlediting.ui.extension;

import org.eclipse.jface.text.TextAttribute;
import org.eclipse.jface.text.presentation.IPresentationDamager;
import org.eclipse.jface.text.presentation.IPresentationReconciler;
import org.eclipse.jface.text.presentation.IPresentationRepairer;
import org.eclipse.jface.text.presentation.PresentationReconciler;
import org.eclipse.jface.text.rules.DefaultDamagerRepairer;
import org.eclipse.swt.widgets.Display;
import org.eclipse.swt.graphics.*;

public class JMLPresentationReconciler extends PresentationReconciler {
   /**
    * the {@link IPresentationReconciler} the JavaEditor is using
    */
   private DefaultDamagerRepairer dr;
   private IPresentationReconciler javaEditorPresentationReconciler;
   
   /**
    * Creates an Instance of JMLPresentationReconciler
    * @param javaEditorPresentationReconciler the IPresentationReconciler the javaEditor uses
    */
   public JMLPresentationReconciler(IPresentationReconciler javaEditorPresentationReconciler) {
      super();
      this.javaEditorPresentationReconciler=javaEditorPresentationReconciler;
      JMLPartitionScanner ps = new JMLPartitionScanner();
      dr= new DefaultDamagerRepairer(new SingleTokenScanner(new TextAttribute(new Color(Display.getCurrent(),new RGB(255,0,0)))));
      this.setDamager(dr,ps.JMLSingleLine);
      this.setDamager(dr, ps.JMLMultiLine);
      this.setRepairer(dr, ps.JMLSingleLine);
      this.setRepairer(dr, ps.JMLSingleLine);
      //
   }
   
   /**
    * Returns a damager for the requested ContentType, redirects to the OriginalJavaEditor Reconciler
    * for other than JML ContentTypes
    * @param contentType the contentType for which the Damager is requested
    * @return a Damager for the specific Content Type
    */
   @Override
   public IPresentationDamager getDamager(String contentType) {
     if(!contentType.equals("JML_MULTI_LINE"))
         if(!contentType.equals("JML_SINGLE_LINE"))
            return javaEditorPresentationReconciler.getDamager(contentType);
     return dr;
   }
   
   /**
    * Returns a repairer for the requestedContentType, redirects to the OriginalJavaEditor Reconciler
    * for other than JML ContentTypes
    * @param contentType the contentType for which the Repairer is requested
    * @return a Repairer for the specific Content Type
    */
   @Override
   public IPresentationRepairer getRepairer(String contentType) {
      if(!contentType.equals("JML_MULTI_LINE"))
         if(!contentType.equals("JML_SINGLE_LINE"))
            return javaEditorPresentationReconciler.getRepairer(contentType);
      return dr;
   }
   
   
}
