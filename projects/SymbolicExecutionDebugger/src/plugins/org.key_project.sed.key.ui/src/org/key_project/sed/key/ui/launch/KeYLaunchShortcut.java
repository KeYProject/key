package org.key_project.sed.key.ui.launch;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.DebugUITools;
import org.eclipse.debug.ui.ILaunchShortcut;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.internal.ui.actions.SelectionConverter;
import org.eclipse.jdt.internal.ui.javaeditor.JavaEditor;
import org.eclipse.jface.text.ITextSelection;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.IStructuredSelection;
import org.eclipse.ui.IEditorPart;
import org.key_project.key4eclipse.util.java.ObjectUtil;
import org.key_project.sed.core.util.LaunchUtil;
import org.key_project.sed.key.core.util.KeySEDUtil;
import org.key_project.sed.key.ui.util.LogUtil;
import org.key_project.sed.ui.util.LaunchUIUtil;

/**
 * {@link ILaunchShortcut} implementation for Symbolic Executiong Debugger
 * based on KeY.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class KeYLaunchShortcut implements ILaunchShortcut {
    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(ISelection selection, String mode) {
        try {
            if (selection instanceof IStructuredSelection && !selection.isEmpty()) {
                Object element = ((IStructuredSelection)selection).getFirstElement();
                if (element instanceof IMethod) {
                    launch((IMethod)element, mode);
                }
            }
        }
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(null, e);
        }
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void launch(IEditorPart editor, String mode) {
        try {
            if (editor instanceof JavaEditor) {
                JavaEditor javaEditor = (JavaEditor)editor;
                if (javaEditor.getSelectionProvider() != null) {
                    ISelection selection = javaEditor.getSelectionProvider().getSelection();
                    if (selection instanceof ITextSelection) {
                        IJavaElement element = SelectionConverter.resolveEnclosingElement(javaEditor, (ITextSelection)selection);
                        if (element instanceof IMethod) {
                            launch((IMethod)element, mode);
                        }
                    }
                }
            }
        }
        catch (Exception e) {
            LogUtil.getLogger().logError(e);
            LogUtil.getLogger().openErrorDialog(null, e);
        }
    }
    
    /**
     * Launches the given {@link IMethod}.
     * @param method The {@link IMethod} to launch.
     * @param mode The mode to use.
     */
    protected void launch(IMethod method, String mode) {
        try {
            ILaunchConfiguration config = findLaunchConfiguration(method);
            if (config == null) {
                config = createConfiguration(method);
            }
            if (config != null) {
                DebugUITools.launch(config, mode);
            }
        }
        catch (OperationCanceledException e) {
            // Nothing to do
        }
    }
    
    /**
     * Tries to find an existing {@link ILaunchConfiguration} for the
     * given {@link IMethod}. If multiple {@link ILaunchConfiguration} exists
     * the user is asked to select one.
     * @param method The {@link IMethod} for that an {@link ILaunchConfiguration} is needed.
     * @return The found {@link ILaunchConfiguration} or {@code null} if no one was found.
     * @throws OperationCanceledException When the user has canceled the select dialog.
     */
    protected ILaunchConfiguration findLaunchConfiguration(IMethod method) {
        List<ILaunchConfiguration> candidateConfigs;
        try {
            // Get parameters
            String projectLabel = KeySEDUtil.getProjectValue(method);
            String typeLabel = KeySEDUtil.getTypeValue(method);
            String methodLabel = KeySEDUtil.getMethodValue(method);
            // Compare existing configurations to with the parameters.
            ILaunchConfiguration[] configs = DebugPlugin.getDefault().getLaunchManager().getLaunchConfigurations(getConfigurationType());
            candidateConfigs = new ArrayList<ILaunchConfiguration>(configs.length);
            for (ILaunchConfiguration config : configs) {
                if (ObjectUtil.equals(projectLabel, KeySEDUtil.getProjectValue(config)) &&
                    ObjectUtil.equals(typeLabel, KeySEDUtil.getTypeValue(config)) &&
                    ObjectUtil.equals(methodLabel, KeySEDUtil.getMethodValue(config))) {
                    candidateConfigs.add(config);
                }
            }
        }
        catch (CoreException e) {
            LogUtil.getLogger().logError(e);
            candidateConfigs = Collections.emptyList();
        }
        int candidateCount = candidateConfigs.size();
        if (candidateCount == 1) {
            return (ILaunchConfiguration)candidateConfigs.get(0);
        }
        else if (candidateCount > 1) {
            ILaunchConfiguration choosen = LaunchUIUtil.chooseConfiguration(candidateConfigs, "Symbolic Execution Debugger (SED)");
            if (choosen == null) {
                throw new OperationCanceledException();
            }
            return choosen;
        }
        else {
            return null;
        }
    }
    
    /**
     * Creates a new {@link ILaunchConfiguration}.
     * @param method The {@link IMethod} to launch.
     * @return The new created {@link ILaunchConfiguration}.
     */
    protected ILaunchConfiguration createConfiguration(IMethod method) {
        ILaunchConfiguration config = null;
        ILaunchConfigurationWorkingCopy wc = null;
        try {
            ILaunchConfigurationType configType = getConfigurationType();
            String typeLabel = KeySEDUtil.getTypeValue(method);
            String methodLabel = KeySEDUtil.getMethodValue(method);
            wc = configType.newInstance(null, LaunchUtil.getLaunchManager().generateLaunchConfigurationName(typeLabel + "#" + methodLabel));
            wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PROJECT, KeySEDUtil.getProjectValue(method));
            wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_TYPE, typeLabel);
            wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD, methodLabel);
            wc.setMappedResources(new IResource[] {method.getUnderlyingResource()});
            config = wc.doSave();
        }
        catch (CoreException exception) {
            LogUtil.getLogger().logError(exception);
        } 
        return config;
    }
    
    /**
     * Returns the used {@link ILaunchConfigurationType}.
     * @return The used {@link ILaunchConfigurationType}.
     */
    protected ILaunchConfigurationType getConfigurationType() {
        return LaunchUtil.getConfigurationType(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ID);            
    }
}
