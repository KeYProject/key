package org.key_project.sed.ui.visualization.object_diagram.editor;

import org.eclipse.graphiti.ui.editor.DiagramEditor;
import org.key_project.sed.ui.visualization.util.PaletteHideableDiagramEditor;

/**
 * {@link DiagramEditor} for Object Diagrams.
 * @author Martin Hentschel
 */
public class ObjectDiagramEditor extends PaletteHideableDiagramEditor {
   /**
    * The ID of this editor.
    */
   public static final String EDITOR_ID = "org.key_project.sed.ui.visualization.ObjectDiagramEditor";
   
   /**
    * Constructor.
    */
   public ObjectDiagramEditor() {
      setGlobalEnabled(true);
      setDefaultSelectionSynchronizationEnabled(false);
   }
}
