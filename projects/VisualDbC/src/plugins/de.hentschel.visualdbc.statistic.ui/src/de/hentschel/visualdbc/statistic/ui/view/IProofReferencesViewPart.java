package de.hentschel.visualdbc.statistic.ui.view;

import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Control;
import org.eclipse.ui.IEditorPart;

/**
 * Provides the content that is shown in a {@link ProofReferencesViewPart}.
 * The {@link ProofReferencesViewPart} gets the {@link IProofReferencesViewPart} to
 * show from the active {@link IEditorPart} by using the adapter concept
 * ({@link IEditorPart#getAdapter(Class)}).
 * @author Martin Hentschel
 */
public interface IProofReferencesViewPart {
   /**
    * Creates the {@link Control} to show.
    * @param parent The parent {@link Composite}.
    * @return The created {@link Control}.
    */
   public Control createControl(Composite parent);
}
