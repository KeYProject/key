package org.key_project.sed.key.ui.slicing;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Composite;
import org.key_project.sed.core.slicing.ISESlicer;
import org.key_project.sed.key.core.slicing.AbstractKeYSlicer;
import org.key_project.sed.ui.slicing.ISlicingSettingsControlFactory;

/**
 * Factory to create {@link KeYSlicingSettingsControl}s.
 * @author Martin Hentschel
 */
public class KeYSlicingSettingsControlFactory implements ISlicingSettingsControlFactory {
   /**
    * {@inheritDoc}
    */
   @Override
   public boolean isSlicerSupported(ISESlicer slicer) {
      return slicer instanceof AbstractKeYSlicer;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public KeYSlicingSettingsControl createControl(Composite parent) {
      return new KeYSlicingSettingsControl(parent, SWT.NONE);
   }
}
