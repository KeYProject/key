package org.key_project.sed.ui.visualization.object_diagram.editor;

/**
 * Read-only {@link ObjectDiagramEditor}.
 * @author Martin Hentschel
 */
public class ReadonlyObjectDiagramEditor extends ObjectDiagramEditor {
   /**
    * The ID of this editor.
    */
   public static final String EDITOR_ID = "org.key_project.sed.ui.visualization.ReadonlyObjectDiagramEditor";

   /**
    * Constructor.
    */
   public ReadonlyObjectDiagramEditor() {
      setPaletteHidden(true);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void configureGraphicalViewer() {
      super.configureGraphicalViewer();
      setGridVisible(false);
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isDirty() {
      return false;
   }
}
