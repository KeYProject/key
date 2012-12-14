package org.key_project.keyide.ui.editor;


import java.beans.PropertyChangeEvent;
import java.beans.PropertyChangeListener;

import org.eclipse.core.runtime.Assert;
import org.eclipse.ui.IEditorInput;
import org.eclipse.ui.IEditorSite;
import org.eclipse.ui.PartInitException;
import org.eclipse.ui.editors.text.TextEditor;
import org.eclipse.ui.views.contentoutline.IContentOutlinePage;
import org.key_project.keyide.ui.editor.input.StringInput;
import org.key_project.keyide.ui.tester.AutoModeTester;
import org.key_project.keyide.ui.views.Outline;
import org.key_project.keyide.ui.views.StrategyPropertiesView;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.ConsoleUserInterface;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;



/**
 * This class represents the Editor for viewing KeY-Proofs
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
public class KeYEditor extends TextEditor implements IProofEnvironmentProvider {
   public static final String EDITOR_ID = "org.key_project.keyide.ui.editor";
   
   private Outline outline;

   /**
    * Listens for changes on {@link ConsoleUserInterface#isAutoMode()} 
    * of the {@link ConsoleUserInterface} provided via {@link #getKeYEnvironment()}.
    */
   private PropertyChangeListener autoModeActiveListener = new PropertyChangeListener() {
      @Override
      public void propertyChange(PropertyChangeEvent evt) {
         AutoModeTester.updateProperties();
      }
   };

   /**
    * {@inheritDoc}
    */
   @Override
   public void init(IEditorSite site, IEditorInput input) throws PartInitException {
      super.init(site, input);
      getKeYEnvironment().getUi().addPropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public void dispose() {
      getKeYEnvironment().getUi().removePropertyChangeListener(ConsoleUserInterface.PROP_AUTO_MODE, autoModeActiveListener);
      super.dispose();
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public KeYEnvironment<CustomConsoleUserInterface> getKeYEnvironment() {
      Assert.isTrue(getEditorInput() instanceof StringInput);
      return ((StringInput)getEditorInput()).getEnvironment();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Proof getProof() {
      Assert.isTrue(getEditorInput() instanceof StringInput);
      return ((StringInput)getEditorInput()).getProof();
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
      if (IContentOutlinePage.class.equals(adapter)) {
         synchronized (this) {
            if (outline == null) {
               outline = new Outline(getProof(), getKeYEnvironment());
            }
          
         }
         return outline;
      }
      if(StrategyPropertiesView.class.equals(adapter)){
         return getProof();
      }
//      if(IPropertySheetPage.class.equals(adapter)){ // TODO: Remove uncommented code if no longer required, because otherwise it is hard to say in the future why this code was uncommented.
//         synchronized (this) {
//            if (property == null) {
//               property = new StrategyProperties();
//            }
//          
//         }
//         return property;
//      }
      else if (IProofEnvironmentProvider.class.equals(adapter)) {
         return this;
      }
//      if (IProofAutomation.class.equals(adapter)) { // TODO: Remove uncommented code if no longer required, because otherwise it is hard to say in the future why this code was uncommented.
//         return this;
//      }
//      else if (Contento)
      else {
         return super.getAdapter(adapter);
      }
   } 
}
