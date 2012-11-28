package org.key_project.keyide.ui.editor;


import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.keyide.ui.views.Outline;

import de.uka.ilkd.key.proof.Proof;



/**
 * This class represents the Editor for viewing KeY-Proofs
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class KeYEditor extends TextEditor {
   private Outline outline;

   /**
    * Constructor.
    */
   public KeYEditor(){
     
   }
   
   public Proof getProof() {
      return null; // return proof from editor input
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
//      if (IProofAutomation.class.equals(adapter)) {
//         return this;
//      }
//      else if (Contento)
      else {
         return super.getAdapter(adapter);
      }
   } 
}
