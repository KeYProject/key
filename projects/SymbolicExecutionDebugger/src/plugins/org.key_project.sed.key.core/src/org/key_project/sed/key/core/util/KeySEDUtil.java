package org.key_project.sed.key.core.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.util.java.ObjectUtil;
import org.key_project.key4eclipse.util.java.StringUtil;
import org.key_project.key4eclipse.util.jdt.JDTUtil;
import org.key_project.sed.core.util.LaunchUtil;

/**
 * Provides static utility methods for the Symbolic Execution Debugger
 * based on KeY.
 * @author Martin Hentschel
 */
public final class KeySEDUtil {
    /**
     * The ID of the launch configuration type.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ID = "org.key_project.sed.key.core.launch.sed.key";
    
    /**
     * The key of the attribute "project" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PROJECT = "org.key_project.sed.key.core.launch.sed.key.attribute.project";
    
    /**
     * The key of the attribute "type" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_TYPE = "org.key_project.sed.key.core.launch.sed.key.attribute.type";

    /**
     * The key of the attribute "method" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD = "org.key_project.sed.key.core.launch.sed.key.attribute.method";

    /**
     * The key of the attribute "useExistingContract" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_USE_EXISTING_CONTRACT = "org.key_project.sed.key.core.launch.sed.key.attribute.useExistingContract";

    /**
     * The key of the attribute "existingContract" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_EXISTING_CONTRACT = "org.key_project.sed.key.core.launch.sed.key.attribute.existingContract";

    /**
     * The launch mode supported by the Symbolic Execution Debugger based on KeY.
     */
    public static final String MODE = "debug";
    
    /**
     * Forbid instances.
     */
    private KeySEDUtil() {
    }
    
    /**
     * Extracts the project value to store in an {@link ILaunchConfiguration}
     * for the given {@link IMethod}.
     * @param method The given {@link IMethod}.
     * @return The value to store.
     */
    public static String getProjectValue(IMethod method) {
        if (method != null && method.getJavaProject() != null) {
            return method.getJavaProject().getElementName();
        }
        else {
            return null;
        }
    }
    
    /**
     * Extracts the type value to store in an {@link ILaunchConfiguration}
     * for the given {@link IMethod}.
     * @param method The given {@link IMethod}.
     * @return The value to store.
     */
    public static String getTypeValue(IMethod method) {
        if (method != null && method.getParent() instanceof IType) {
            return ((IType)method.getParent()).getFullyQualifiedName();
        }
        else {
            return null;
        }
    }
    
    /**
     * Extracts the method value to store in an {@link ILaunchConfiguration}
     * for the given {@link IMethod}.
     * @param method The given {@link IMethod}.
     * @return The value to store.
     * @throws JavaModelException Occurred Exception
     */
    public static String getMethodValue(IMethod method) throws JavaModelException {
        if (method != null) {
            return JDTUtil.getQualifiedMethodLabel(method);
        }
        else {
            return null;
        }
    }
    
    /**
     * Returns the project attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The project attribute value.
     * @throws CoreException Occurred Exception.
     */
    public static String getProjectValue(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PROJECT, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
    }
    
    /**
     * Returns the type attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The type attribute value.
     * @throws CoreException Occurred Exception.
     */
    public static String getTypeValue(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_TYPE, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
    }
    
    /**
     * Returns the method attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The method attribute value.
     * @throws CoreException Occurred Exception.
     */
    public static String getMethodValue(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
    }
    
    /**
     * Returns the use existing contract attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The use existing contract attribute value.
     * @throws CoreException Occurred Exception.
     */
    public static boolean isUseExistingContractValue(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_USE_EXISTING_CONTRACT, false) : false;
    }
    
    /**
     * Returns the existing contract attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The existing contract attribute value.
     * @throws CoreException Occurred Exception.
     */
    public static String getExistingContractValue(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_EXISTING_CONTRACT, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
    }
    
    /**
     * Searches the {@link IMethod} that is defined by the given {@link ILaunch}.
     * @param launch The {@link ILaunch} that defines an {@link IMethod}.
     * @return The found {@link IMethod} or {@code null} if no one was found.
     * @throws CoreException Occurred Exception.
     */
    public static IMethod findMethod(ILaunch launch) throws CoreException {
        if (launch != null) {
            return findMethod(launch.getLaunchConfiguration());
        }
        else {
            return null;
        }
    }
    
    /**
     * Searches the {@link IMethod} that is defined by the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} that defines an {@link IMethod}.
     * @return The found {@link IMethod} or {@code null} if no one was found.
     * @throws CoreException Occurred Exception.
     */
    public static IMethod findMethod(ILaunchConfiguration configuration) throws CoreException {
        IMethod result = null;
        if (configuration != null) {
            String projectName = getProjectValue(configuration);
            IJavaProject project = JDTUtil.getJavaProject(projectName);
            if (project != null) {
                String typeName = getTypeValue(configuration);
                IType type = project.findType(typeName);
                if (type != null) {
                    String methodSignature = getMethodValue(configuration);
                    result = JDTUtil.getElementForQualifiedMethodLabel(type.getMethods(), methodSignature);
                }
            }
        }
        return result;
    }
    
    /**
     * Returns the used {@link ILaunchConfigurationType}.
     * @return The used {@link ILaunchConfigurationType}.
     */
    public static ILaunchConfigurationType getConfigurationType() {
        return LaunchUtil.getConfigurationType(LAUNCH_CONFIGURATION_TYPE_ID);            
    }
    
    /**
     * Creates a new {@link ILaunchConfiguration}.
     * @param method The {@link IMethod} to launch.
     * @return The new created {@link ILaunchConfiguration}.
     * @throws CoreException Occurred Exception.
     */
    public static ILaunchConfiguration createConfiguration(IMethod method) throws CoreException {
        ILaunchConfiguration config = null;
        ILaunchConfigurationWorkingCopy wc = null;
        ILaunchConfigurationType configType = getConfigurationType();
        String typeLabel = KeySEDUtil.getTypeValue(method);
        String methodLabel = KeySEDUtil.getMethodValue(method);
        wc = configType.newInstance(null, LaunchUtil.getLaunchManager().generateLaunchConfigurationName(typeLabel + "#" + methodLabel));
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PROJECT, KeySEDUtil.getProjectValue(method));
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_TYPE, typeLabel);
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD, methodLabel);
        wc.setMappedResources(new IResource[] {method.getUnderlyingResource()});
        config = wc.doSave();
        return config;
    }
    
    /**
     * Searches all {@link ILaunchConfiguration} that handles
     * the given {@link IMethod}.
     * @param method The {@link IMethod} for that {@link ILaunchConfiguration}s are required.
     * @return The found {@link ILaunchConfiguration}s.
     * @throws CoreException Occurred Exception.
     */
    public static List<ILaunchConfiguration> searchLaunchConfigurations(IMethod method) throws CoreException {
        // Get parameters
        String projectLabel = KeySEDUtil.getProjectValue(method);
        String typeLabel = KeySEDUtil.getTypeValue(method);
        String methodLabel = KeySEDUtil.getMethodValue(method);
        // Compare existing configurations to with the parameters.
        ILaunchConfiguration[] configs = DebugPlugin.getDefault().getLaunchManager().getLaunchConfigurations(KeySEDUtil.getConfigurationType());
        List<ILaunchConfiguration> result = new ArrayList<ILaunchConfiguration>(configs.length);
        for (ILaunchConfiguration config : configs) {
            if (ObjectUtil.equals(projectLabel, KeySEDUtil.getProjectValue(config)) &&
                ObjectUtil.equals(typeLabel, KeySEDUtil.getTypeValue(config)) &&
                ObjectUtil.equals(methodLabel, KeySEDUtil.getMethodValue(config))) {
                result.add(config);
            }
        }
        return result;
    }
}
