package org.key_project.util.eclipse.preference.event;

import java.util.EventListener;

import org.eclipse.jface.preference.FieldEditor;

/**
 * Allows to observe the shown value of a {@link FieldEditor}.
 * @author Martin Hentschel
 */
public interface IFieldEditorValueListener extends EventListener {
   /**
    * When the shown value has changed.
    * @param e The event.
    */
   public void shownValueChanged(FieldEditorValueEvent e);
}
