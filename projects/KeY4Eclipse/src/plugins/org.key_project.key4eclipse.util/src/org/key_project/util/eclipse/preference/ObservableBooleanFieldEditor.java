package org.key_project.util.eclipse.preference;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.preference.BooleanFieldEditor;
import org.eclipse.swt.events.SelectionAdapter;
import org.eclipse.swt.events.SelectionEvent;
import org.eclipse.swt.widgets.Composite;
import org.key_project.util.eclipse.preference.event.FieldEditorValueEvent;
import org.key_project.util.eclipse.preference.event.IFieldEditorValueListener;

/**
 * An observable {@link BooleanFieldEditor}.
 * @author Martin Hentschel
 */
public class ObservableBooleanFieldEditor extends BooleanFieldEditor {
   /**
    * All registered {@link IFieldEditorValueListener}.
    */
   private List<IFieldEditorValueListener> fieldEditorValueListener = new LinkedList<IFieldEditorValueListener>();
   
   /**
    * Constructor.
    * @param name the name of the preference this field editor works on
    * @param label the label text of the field editor
    * @param parent the parent of the field editor's control
    */
   public ObservableBooleanFieldEditor(String name, String label, Composite parent) {
      super(name, label, parent);
   }

   /**
    * Constructor.
    * @param name the name of the preference this field editor works on
    * @param labelText the label text of the field editor
    * @param style the style, either <code>DEFAULT</code> or <code>SEPARATE_LABEL</code>
    * @param parent the parent of the field editor's control
    */
   public ObservableBooleanFieldEditor(String name, String labelText, int style, Composite parent) {
      super(name, labelText, style, parent);
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void doFillIntoGrid(Composite parent, int numColumns) {
      super.doFillIntoGrid(parent, numColumns);
      getChangeControl(parent).addSelectionListener(new SelectionAdapter() {
         @Override
         public void widgetSelected(SelectionEvent e) {
            fireShownValueChanged(new FieldEditorValueEvent(ObservableBooleanFieldEditor.this));
         }
      });
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected void doLoad() {
      super.doLoad();
      fireShownValueChanged(new FieldEditorValueEvent(this));
   }

   /**
    * {@inheritDoc}
    */
   @Override
   protected void doLoadDefault() {
      super.doLoadDefault();
      fireShownValueChanged(new FieldEditorValueEvent(this));
   }

   /**
    * Registers the given {@link IFieldEditorValueListener}.
    * @param l The {@link IFieldEditorValueListener} to register.
    */
   public void addFieldEditorValueListener(IFieldEditorValueListener l) {
      if (l != null) {
         fieldEditorValueListener.add(l);
      }
   }
   
   /**
    * Unregisters the given {@link IFieldEditorValueListener}.
    * @param l The {@link IFieldEditorValueListener} to unregister.
    */
   public void removeFieldEditorValueListener(IFieldEditorValueListener l) {
      if (l != null) {
         fieldEditorValueListener.remove(l);
      }
   }
   
   /**
    * Returns all registered {@link IFieldEditorValueListener}.
    * @return All registered {@link IFieldEditorValueListener}.
    */
   public IFieldEditorValueListener[] getFieldEditorValueListener() {
      return fieldEditorValueListener.toArray(new IFieldEditorValueListener[fieldEditorValueListener.size()]);
   }
   
   /**
    * Fires the even to all registered {@link IFieldEditorValueListener}.
    * @param e The event to fire.
    */
   protected void fireShownValueChanged(FieldEditorValueEvent e) {
      IFieldEditorValueListener[] toInform = getFieldEditorValueListener();
      for (IFieldEditorValueListener l : toInform) {
         l.shownValueChanged(e);
      }
   }
}
