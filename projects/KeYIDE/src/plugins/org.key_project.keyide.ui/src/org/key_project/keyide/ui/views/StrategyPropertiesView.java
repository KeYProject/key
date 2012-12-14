package org.key_project.keyide.ui.views;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPart;
import org.key_project.keyide.ui.editor.KeYEditor2;
import org.key_project.keyide.ui.providers.StrategyContentProvider;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;

import de.uka.ilkd.key.proof.Proof;

public class StrategyPropertiesView extends AbstractViewBasedView{

   private StrategyContentProvider form;
   
   private Proof proof;
   
   
   public StrategyPropertiesView(){
      
   }
   
   public StrategyPropertiesView(Proof proof) {
      this.proof=proof;
   }

   @Override
   public void createPartControl(Composite parent) {
      form=new StrategyContentProvider(parent);
      form.setProof(proof);
   }

   @Override
   public void setFocus() {
   }

   @Override
   protected boolean shouldHandleBaseView(IViewPart baseView) {
      return true;
   }

   @Override
   protected void handleBaseViewChanged(IViewPart oldBaseView,
         IViewPart newBaseView) {
   }

   @Override
   protected void handlePartOpened(IWorkbenchPart part) {
      super.handlePartActivated(part);
      if (part instanceof IEditorPart) {
         if(part instanceof KeYEditor2){
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
         if(part instanceof KeYEditor2){
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