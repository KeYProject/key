package org.key_project.sed.key.core.util;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.key_project.key4eclipse.util.java.StringUtil;
import org.key_project.key4eclipse.util.jdt.JDTUtil;

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
    // TODO: Implement test    
    public static String getProjectValue(IMethod method) {
        return method.getJavaProject().getElementName();
    }
    
    /**
     * Extracts the type value to store in an {@link ILaunchConfiguration}
     * for the given {@link IMethod}.
     * @param method The given {@link IMethod}.
     * @return The value to store.
     */
    // TODO: Implement test
    public static String getTypeValue(IMethod method) {
        return ((IType)method.getParent()).getFullyQualifiedName();
    }
    
    /**
     * Extracts the method value to store in an {@link ILaunchConfiguration}
     * for the given {@link IMethod}.
     * @param method The given {@link IMethod}.
     * @return The value to store.
     */
    // TODO: Implement test
    public static String getMethodValue(IMethod method) {
        return JDTUtil.getTextLabel(method);
    }
    
    /**
     * Returns the project attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The project attribute value.
     * @throws CoreException Occurred Exception.
     */
    // TODO: Implement test
    public static String getProjectValue(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PROJECT, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
    }
    
    /**
     * Returns the type attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The type attribute value.
     * @throws CoreException Occurred Exception.
     */
    // TODO: Implement test
    public static String getTypeValue(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_TYPE, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
    }
    
    /**
     * Returns the method attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The method attribute value.
     * @throws CoreException Occurred Exception.
     */
    // TODO: Implement test
    public static String getMethodValue(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
    }

    /**
     * Searches the {@link IMethod} that is defined by the given {@link ILaunch}.
     * @param launch The {@link ILaunch} that defines an {@link IMethod}.
     * @return The found {@link IMethod} or {@code null} if no one was found.
     * @throws CoreException Occurred Exception.
     */
    // TODO: Implement test
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
    // TODO: Implement test
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
                    result = (IMethod)JDTUtil.getElementForTextLabel(type.getMethods(), methodSignature);
                }
            }
        }
        return result;
    }
}
