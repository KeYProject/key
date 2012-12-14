package org.key_project.keyide.ui.views;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;
import org.key_project.keyide.ui.providers.OutlineContentProvider;
import org.key_project.keyide.ui.providers.OutlineLabelProvider;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * A class to display the correct Outline for the current {@link Proof}
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
// TODO: Name is to general, rename into ProofTreeContentOutlinePage
public class Outline extends ContentOutlinePage {
   private Proof proof;
   
   private KeYEnvironment<CustomConsoleUserInterface> environment;
   
   /**
    * Constructor.
    * @param proof The {@link Proof} for this Outline.
    */
   public Outline(Proof proof, KeYEnvironment<CustomConsoleUserInterface> environment) {
      this.proof = proof;
      this.environment = environment;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected int getTreeStyle() {
      return super.getTreeStyle() | SWT.VIRTUAL;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void createControl(Composite parent) {
      super.createControl(parent);
      getTreeViewer().setUseHashlookup(true);
      getTreeViewer().setContentProvider(new OutlineContentProvider(getTreeViewer(), environment, proof));
      getTreeViewer().setLabelProvider(new OutlineLabelProvider(getTreeViewer(), environment, proof));
      getTreeViewer().setInput(proof);
   }
}
