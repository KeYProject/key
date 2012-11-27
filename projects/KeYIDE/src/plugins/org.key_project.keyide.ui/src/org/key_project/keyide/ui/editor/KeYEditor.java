package org.key_project.keyide.ui.editor;


import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;



/**
 * This class represents the Editor for viewing KeY-Proofs
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class KeYEditor extends TextEditor {

   /**
    * Constructor.
    */
   public KeYEditor(){
     
   }

   @Override
   public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
      if (IContentOutlinePage.class.equals(adapter)) {
         return null;
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
