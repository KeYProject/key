package org.key_project.keyide.ui.editor;


import org.eclipse.core.runtime.Assert;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.keyide.ui.editor.input.StringInput;
import org.key_project.keyide.ui.views.Outline;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;



/**
 * This class represents the Editor for viewing KeY-Proofs
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class KeYEditor extends TextEditor implements IProofEnvironmentProvider {
   public static final String EDITOR_ID = "org.key_project.keyide.ui.editor";
   
   private Outline outline;

   /**
    * Constructor.
    */
   public KeYEditor(){
     
   }
   
   @Override
   public KeYEnvironment<?> getKeYEnvironment() {
      Assert.isTrue(getEditorInput() instanceof StringInput);
      return ((StringInput)getEditorInput()).getEnvironment();
   }

   @Override
   public Proof getProof() {
      Assert.isTrue(getEditorInput() instanceof StringInput);
      return ((StringInput)getEditorInput()).getProof();
   }

   @Override
   public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
      if (IContentOutlinePage.class.equals(adapter)) {
         synchronized (this) {
            if (outline == null) {
               outline = new Outline(getProof());
            }
         }
         return outline;
      }
      else if (IProofEnvironmentProvider.class.equals(adapter)) {
         return this;
      }
//      if (IProofAutomation.class.equals(adapter)) {
//         return this;
//      }
//      else if (Contento)
      else {
         return super.getAdapter(adapter);
      }
   } 
}
