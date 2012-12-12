package org.key_project.keyide.ui.views;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.ui.views.contentoutline.ContentOutlinePage;
import org.key_project.keyide.ui.providers.OutlineContentProvider;
import org.key_project.keyide.ui.providers.OutlineLabelProvider;

import de.uka.ilkd.key.proof.Proof;

/**
 * A class to display the correct Outline for the current {@link Proof}
 * 
 * @author Christoph Schneider, Niklas Bunzel, Stefan Käsdorf, Marco Drebing
 */
// TODO: Name is to general, rename into ProofTreeContentOutlinePage
public class Outline extends ContentOutlinePage {
   private Proof proof;
   
   /**
    * Constructor.
    * @param proof The {@link Proof} for this Outline.
    */
   public Outline(Proof proof) {
      this.proof = proof;
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
      getTreeViewer().setContentProvider(new OutlineContentProvider(getTreeViewer()));
      getTreeViewer().setLabelProvider(new OutlineLabelProvider());
      getTreeViewer().setInput(proof);
   }
}
