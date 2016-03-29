package org.key_project.sed.ui.slicing;

import org.eclipse.swt.widgets.Composite;
import org.key_project.sed.core.slicing.ISESlicer;

/**
 * This factory is used to create {@link SlicingSettingsControl}s.
 * @author Martin Hentschel
 */
public interface ISlicingSettingsControlFactory {
   /**
    * Checks if the given {@link ISESlicer} is supported.
    * @param slicer The {@link ISESlicer} to check.
    * @return {@code true} is supported, {@code false} is not supported.
    */
   public boolean isSlicerSupported(ISESlicer slicer);
   
   /**
    * Creates a {@link SlicingSettingsControl}.
    * @param parent The parent {@link Composite}.
    * @return The created {@link SlicingSettingsControl}.
    */
   public SlicingSettingsControl createControl(Composite parent);
}
