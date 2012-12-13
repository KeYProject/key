package org.key_project.keyide.ui.views;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.events.SelectionListener;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.layout.RowLayout;
import org.eclipse.swt.widgets.Button;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.Group;
import org.eclipse.swt.widgets.Listener;
import org.eclipse.swt.widgets.Scale;
import org.eclipse.ui.IEditorPart;
import org.eclipse.ui.IViewPart;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.forms.widgets.FormToolkit;
import org.eclipse.ui.forms.widgets.ScrolledForm;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.keyide.ui.providers.StrategyContentProvider;
import org.key_project.util.eclipse.swt.view.AbstractBeanViewPart;
import org.key_project.util.eclipse.swt.view.AbstractViewBasedView;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

public class StrategyPropertiesView extends AbstractViewBasedView{

   private FormToolkit toolkit;
   
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
      // TODO Auto-generated method stub

   }

   @Override
   protected boolean shouldHandleBaseView(IViewPart baseView) {
      // TODO Auto-generated method stub
      return true;
   }

   @Override
   protected void handleBaseViewChanged(IViewPart oldBaseView,
         IViewPart newBaseView) {
      // TODO Auto-generated method stub
      
   }

   @Override
   protected void handlePartOpened(IWorkbenchPart part) {
      super.handlePartActivated(part);
      if (part instanceof IEditorPart) {
         if(part instanceof KeYEditor){
            form.setEnabled(true);
            Object obj = part.getAdapter(this.getClass());
            if(obj instanceof Proof){
               System.out.println("opened");
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
               System.out.println("activated");
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