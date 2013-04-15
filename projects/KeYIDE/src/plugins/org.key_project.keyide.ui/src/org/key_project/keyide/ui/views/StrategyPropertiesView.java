package org.key_project.keyide.ui.views;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IViewReference;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.providers.StrategyContentProvider;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;

import de.uka.ilkd.key.proof.Proof;

// TODO: Document this class
public class StrategyPropertiesView extends AbstractViewBasedView {

   private StrategyContentProvider form;
   
   private Proof proof;
   
   
   public StrategyPropertiesView(){
      
   }
   
   public StrategyPropertiesView(Proof proof) {
      this.proof = proof;
   }

   @Override
   public void createPartControl(Composite parent) {
      form = new StrategyContentProvider(parent);
      form.setProof(proof);
   }

   @Override
   public void setFocus() {
      if (form != null && !form.isDisposed()) {
         form.setFocus();
      }
   }

   @Override
   protected boolean shouldHandleBaseView(IViewPart baseView) {
      return false;
   }

   @Override
   protected boolean shouldHandleBaseViewReference(IViewReference baseViewReference) {
      return false;
   }

   @Override
   protected void handleBaseViewChanged(IViewPart oldBaseView, IViewPart newBaseView) {
      // Nothing to do
   }

   // TODO: Content of handlePartOpened and handlePartActivated is the same, refactor in one method which is called by both
   @Override
   protected void handlePartOpened(IWorkbenchPart part) {
      super.handlePartActivated(part);
      if (part instanceof IEditorPart) {
         if(part instanceof KeYEditor){
            form.setEnabled(true);
            Object obj = part.getAdapter(this.getClass());
            if(obj instanceof Proof){
               proof = (Proof) obj;
               form.setProof((Proof)obj);
               form.setContent();
            }
         }
         else{
            form.setEnabled(false);
         }
      }
   }

   @Override
   protected void handlePartActivated(IWorkbenchPart part) {
      super.handlePartActivated(part);
      if (part instanceof IEditorPart) {
         if(part instanceof KeYEditor){
            form.setEnabled(true);
            Object obj = part.getAdapter(this.getClass());
            if(obj instanceof Proof){
               proof = (Proof) obj;
               form.setProof((Proof)obj);
               form.setContent();
            }
         }
         else{
            form.setEnabled(false);
         }
      }
   }
}