package de.hentschel.visualdbc.statistic.ui.view;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorPart;

import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.statistic.ui.control.IProofReferenceProvider;
import de.hentschel.visualdbc.statistic.ui.control.ProofReferenceComposite;

/**
 * Implementation of {@link IProofReferencesViewPart} to show proof references of
 * {@link DbcModel}s.
 * @author Martin Hentschel
 */
public class DbcProofReferencesViewPart implements IProofReferencesViewPart {
   /**
    * The {@link IEditorPart} which provides the content.
    */
   private IEditorPart editor;
   
   /**
    * The {@link IProofReferenceProvider} to use.
    */
   private IProofReferenceProvider proofReferenceProvider;
   
   /**
    * Constructor.
    * @param editor The {@link IEditorPart} which provides the content.
    * @param proofReferenceProvider The {@link IProofReferenceProvider} to use.
    */
   public DbcProofReferencesViewPart(IEditorPart editor, IProofReferenceProvider proofReferenceProvider) {
      this.editor = editor;
      this.proofReferenceProvider = proofReferenceProvider;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Control createControl(Composite parent) {
      return new ProofReferenceComposite(parent, SWT.NONE, editor, proofReferenceProvider);
   }
}
