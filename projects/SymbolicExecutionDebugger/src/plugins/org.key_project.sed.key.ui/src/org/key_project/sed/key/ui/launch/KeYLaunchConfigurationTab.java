package org.key_project.sed.key.ui.launch;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.AbstractLaunchConfigurationTab;
import org.eclipse.swt.SWT;
import org.eclipse.swt.events.ModifyEvent;
import org.eclipse.swt.events.ModifyListener;
import org.eclipse.swt.layout.GridData;
import org.eclipse.swt.layout.GridLayout;
import org.eclipse.swt.widgets.Composite;
import org.eclipse.swt.widgets.Label;
import org.eclipse.swt.widgets.Text;

/**
 * {@link AbstractLaunchConfigurationTab} implementation for the
 * Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class KeYLaunchConfigurationTab extends AbstractLaunchConfigurationTab {
    /**
     * Contains the example value.
     */
    private Text valueText;

    /**
     * {@inheritDoc}
     */
    @Override
    public void createControl(Composite parent) {
        Composite rootComposite = new Composite(parent, SWT.NONE);
        setControl(rootComposite);
        rootComposite.setLayout(new GridLayout(2, false));
        Label label = new Label(rootComposite, SWT.NONE);
        label.setText("A value");
        valueText = new Text(rootComposite, SWT.BORDER);
        valueText.setLayoutData(new GridData(GridData.FILL_HORIZONTAL));
        valueText.addModifyListener(new ModifyListener() {
            @Override
            public void modifyText(ModifyEvent e) {
                    updateLaunchConfigurationDialog();
            }
         });
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void setDefaults(ILaunchConfigurationWorkingCopy configuration) {
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void initializeFrom(ILaunchConfiguration configuration) {
        try {
            valueText.setText(configuration.getAttribute("key", "Hello World"));
        } 
        catch (CoreException e) {
            e.printStackTrace();
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void performApply(ILaunchConfigurationWorkingCopy configuration) {
        configuration.setAttribute("key", valueText.getText());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getName() {
        return "Main";
    }
    
    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isValid(ILaunchConfiguration launchConfig) {
        boolean valid = super.isValid(launchConfig);
        if (valid && valueText.getText().isEmpty()) {
            valid = false;
            setErrorMessage("Value is empty.");
        }
        if (valid) {
            setErrorMessage(null);
        }
        return valid;
    }
}
