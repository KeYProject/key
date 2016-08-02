package org.key_project.sed.ui.slicing;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.model.IVariable;
import org.eclipse.swt.widgets.Composite;
import org.key_project.sed.core.model.ISENode;
import org.key_project.sed.core.model.ISEVariable;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.sed.ui.slicing.event.ISlicingSettingsControlListener;
import org.key_project.sed.ui.slicing.event.SlicingSettingsControlEvent;

/**
 * Instances of this class are used to edit the settings specific to an {@link ISESlicer}.
 * @author Martin Hentschel
 */
public abstract class SlicingSettingsControl extends Composite {
   /**
    * The available {@link ISlicingSettingsControlListener}s.
    */
   private final List<ISlicingSettingsControlListener> listeners = new LinkedList<ISlicingSettingsControlListener>();
   
   /**
    * Constructor.
    * @param parent The parent {@link Composite}.
    * @param style The style to use.
    */
   public SlicingSettingsControl(Composite parent, int style) {
      super(parent, style);
   }
   
   /**
    * Initializes the settings.
    * @param seedNode The seed {@link ISENode}.
    * @param seedVariable The seed {@link IVariable}.
    * @param monitor The {@link IProgressMonitor} to use.
    */
   public abstract void init(ISENode seedNode, 
                             ISEVariable seedVariable, 
                             IProgressMonitor monitor) throws DebugException;
   
   /**
    * Validates the current settings.
    * @return The error message or {@code null} if all settings are valid.
    */
   public abstract String validateSettings();
   
   /**
    * Returns the selected settings.
    * @return The selected settings.
    */
   public abstract Object getSelectedSettings();
   
   /**
    * Registers the given {@link ISlicingSettingsControlListener}.
    * @param l The {@link ISlicingSettingsControlListener} to add.
    */
   public void addSlicingSettingsControlListener(ISlicingSettingsControlListener l) {
      listeners.add(l);
   }
   
   /**
    * Unregisters the given {@link ISlicingSettingsControlListener}.
    * @param l The {@link ISlicingSettingsControlListener} to remove.
    */
   public void removeSlicingSettingsControlListener(ISlicingSettingsControlListener l) {
      listeners.remove(l);
   }
   
   /**
    * Returns all available {@link ISlicingSettingsControlListener}.
    * @return The available {@link ISlicingSettingsControlListener}.
    */
   public ISlicingSettingsControlListener[] getSlicingSettingsControlListener() {
      return listeners.toArray(new ISlicingSettingsControlListener[listeners.size()]);
   }
   
   /**
    * Fires {@link ISlicingSettingsControlListener#settingsChanged(SlicingSettingsControlEvent)}.
    * @param e The {@link SlicingSettingsControlEvent} to fire.
    */
   protected void fireSettingsChanged(SlicingSettingsControlEvent e) {
      ISlicingSettingsControlListener[] listeners = getSlicingSettingsControlListener();
      for (ISlicingSettingsControlListener l : listeners) {
         l.settingsChanged(e);
      }
   }
}
