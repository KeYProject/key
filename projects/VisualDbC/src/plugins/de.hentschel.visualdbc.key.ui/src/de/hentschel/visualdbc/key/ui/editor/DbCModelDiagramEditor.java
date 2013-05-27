package de.hentschel.visualdbc.key.ui.editor;

import org.eclipse.ui.IEditorInput;

import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;

/**
 * Extends the functionality of {@link DbCDiagramEditor} to support {@link DbcModelEditorInput}s.
 * @author Martin Hentschel
 */
public class DbCModelDiagramEditor extends DbCDiagramEditor {
   /**
    * Constructor.
    */
   public DbCModelDiagramEditor() {
      super();
   }

   /**
    * Constructor.
    * @param hasFlyoutPalette Show palette?
    */
   public DbCModelDiagramEditor(boolean hasFlyoutPalette) {
      super(hasFlyoutPalette);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void setDocumentProvider(IEditorInput input) {
      setDocumentProvider(new DbCModelDocumentProvider());
   }
}
