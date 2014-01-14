/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.key.core.util;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.debug.core.DebugException;
import org.eclipse.debug.core.DebugPlugin;
import org.eclipse.debug.core.ILaunch;
import org.eclipse.debug.core.ILaunchConfiguration;
import org.eclipse.debug.core.ILaunchConfigurationType;
import org.eclipse.debug.core.ILaunchConfigurationWorkingCopy;
import org.eclipse.debug.ui.IDebugUIConstants;
import org.eclipse.debug.ui.IDebugView;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.IViewPart;
import org.key_project.sed.core.model.ISEDDebugNode;
import org.key_project.sed.core.model.ISEDDebugTarget;
import org.key_project.sed.core.model.ISEDThread;
import org.key_project.sed.core.util.LaunchUtil;
import org.key_project.util.eclipse.WorkbenchUtil;
import org.key_project.util.eclipse.swt.SWTUtil;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;
import org.key_project.util.java.ObjectUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.speclang.FunctionalOperationContract;

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
     * The key of the attribute "new debug session" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_NEW_DEBUG_SESSION = "org.key_project.sed.key.core.launch.sed.key.attribute.newDebugSession";;

    /**
     * The key of the attribute "file" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_FILE_TO_LOAD = "org.key_project.sed.key.core.launch.sed.key.attribute.fileToLoad";

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
     * The key of the attribute "execute method range" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_EXECUTE_METHOD_RANGE = "org.key_project.sed.key.core.launch.sed.key.attribute.executeMethodRange";

    /**
     * The key of the attribute "method range start line" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_LINE = "org.key_project.sed.key.core.launch.sed.key.attribute.methodRangeStartLine";

    /**
     * The key of the attribute "method range start column" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_COLUMN = "org.key_project.sed.key.core.launch.sed.key.attribute.methodRangeStartColumn";

    /**
     * The key of the attribute "method range end line" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_LINE = "org.key_project.sed.key.core.launch.sed.key.attribute.methodRangeEndLine";

    /**
     * The key of the attribute "method range end column" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_COLUMN = "org.key_project.sed.key.core.launch.sed.key.attribute.methodRangeEndColumn";

    /**
     * The key of the attribute "useExistingContract" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_USE_EXISTING_CONTRACT = "org.key_project.sed.key.core.launch.sed.key.attribute.useExistingContract";

    /**
     * The key of the attribute "existingContract" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_EXISTING_CONTRACT = "org.key_project.sed.key.core.launch.sed.key.attribute.existingContract";

    /**
     * The key of the attribute "precondition" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PRECONDITION = "org.key_project.sed.key.core.launch.sed.key.attribute.precondition";

    /**
     * The key of the attribute "show method return values in debug nodes" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES = "org.key_project.sed.key.core.launch.sed.key.attribute.showMethodReturnValuesInDebugNodes";

    /**
     * The key of the attribute "show variables of selected debug node" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_VARIABLES_OF_SELECTED_DEBUG_NODE = "org.key_project.sed.key.core.launch.sed.key.attribute.showVariablesOfSelectedDebugNode";

    /**
     * The key of the attribute "show KeY's main window" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_KEY_MAIN_WINDOW = "org.key_project.sed.key.core.launch.sed.key.attribute.showKeYMainWindow";

    /**
     * The key of the attribute "merge branch conditions" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_MERGE_BRANCH_CONDITIONS = "org.key_project.sed.key.core.launch.sed.key.attribute.mergeBranchConditions";

    /**
     * The key of the attribute "use pretty printing" in an {@link ILaunchConfiguration} of type {@value KeySEDUtil#LAUNCH_CONFIGURATION_TYPE_ID}.
     */
    public static final String LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_USE_PRETTY_PRINTING = "org.key_project.sed.key.core.launch.sed.key.attribute.usePrettyPrinting";

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
     * Returns the file to load attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The file to load attribute value.
     * @throws CoreException Occurred Exception.
     */
    public static String getFileToLoadValue(ILaunchConfiguration configuration) throws CoreException {
       return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_FILE_TO_LOAD, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
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
     * Returns the precondition attribute value from the given {@link ILaunchConfiguration}.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The precondition attribute value.
     * @throws CoreException Occurred Exception.
     */
    public static String getPrecondition(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PRECONDITION, StringUtil.EMPTY_STRING) : StringUtil.EMPTY_STRING;
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
     * Checks if method return values should be shown in debug nodes.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return {@code true} show method return values, {@code false} do not show method return values.
     * @throws CoreException Occurred Exception.
     */
    public static boolean isShowMethodReturnValuesInDebugNodes(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_METHOD_RETURN_VALUES_IN_DEBUG_NODES, KeYSEDPreferences.isShowMethodReturnValuesInDebugNode()) : KeYSEDPreferences.isShowMethodReturnValuesInDebugNode();
    }
    
    /**
     * Checks if variables of the selected debug node should be shown.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return {@code true} show variables of selected debug node, {@code false} do not show variables of selected debug node.
     * @throws CoreException Occurred Exception.
     */
    public static boolean isShowVariablesOfSelectedDebugNode(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_VARIABLES_OF_SELECTED_DEBUG_NODE, KeYSEDPreferences.isShowVariablesOfSelectedDebugNode()) : KeYSEDPreferences.isShowVariablesOfSelectedDebugNode();
    }
    
    /**
     * Checks if KeY's main window should be shown or not.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return {@code true} show KeY's main window, {@code false} hide KeY's main window
     * @throws CoreException Occurred Exception.
     */
    public static boolean isShowKeYMainWindow(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_SHOW_KEY_MAIN_WINDOW, KeYSEDPreferences.isShowKeYMainWindow()) : KeYSEDPreferences.isShowKeYMainWindow();
    }
    
    /**
     * Checks if branch conditions are merged.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return {@code true} merge branch conditions, {@code false} do not merge branch conditions.
     * @throws CoreException Occurred Exception.
     */
    public static boolean isMergeBranchConditions(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_MERGE_BRANCH_CONDITIONS, KeYSEDPreferences.isMergeBranchConditions()) : KeYSEDPreferences.isMergeBranchConditions();
    }
    
    /**
     * Checks if pretty printing should be used.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return {@code true} use pretty printing, {@code false} do not use pretty printing.
     * @throws CoreException Occurred Exception.
     */
    public static boolean isUsePrettyPrinting(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_USE_PRETTY_PRINTING, KeYSEDPreferences.isUsePrettyPrinting()) : KeYSEDPreferences.isUsePrettyPrinting();
    }

    /**
     * Checks if a new debug session should be started.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return {@code true} start new debug session, {@code false} continue existing *.proof file.
     * @throws CoreException Occurred Exception.
     */
    public static boolean isNewDebugSession(ILaunchConfiguration configuration) throws CoreException {
       return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_NEW_DEBUG_SESSION, true) : true;
    }
    
    /**
     * Checks if a method range should be executed.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return {@code true} execute method range, {@code false} execute complete method.
     * @throws CoreException Occurred Exception.
     */
    public static boolean isExecuteMethodRange(ILaunchConfiguration configuration) throws CoreException {
        return configuration != null ? configuration.getAttribute(LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_EXECUTE_METHOD_RANGE, false) : false;
    }
    
    /**
     * Returns the method range start line.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The method range start line.
     * @throws CoreException Occurred Exception.
     */
    public static int getMethodRangeStartLine(ILaunchConfiguration configuration) throws CoreException {
       return getSaveInt(configuration, LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_LINE, 0);
    }
    
    /**
     * Returns the method range start column.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The method range start column.
     * @throws CoreException Occurred Exception.
     */
    public static int getMethodRangeStartColumn(ILaunchConfiguration configuration) throws CoreException {
       return getSaveInt(configuration, LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_COLUMN, 0);
    }
    
    /**
     * Returns the method range end line.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The method range end line.
     * @throws CoreException Occurred Exception.
     */
    public static int getMethodRangeEndLine(ILaunchConfiguration configuration) throws CoreException {
       return getSaveInt(configuration, LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_LINE, 0);
    }
    
    /**
     * Returns the method range end column.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @return The method range end column.
     * @throws CoreException Occurred Exception.
     */
    public static int getMethodRangeEndColumn(ILaunchConfiguration configuration) throws CoreException {
       return getSaveInt(configuration, LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_COLUMN, 0);
    }
    
    /**
     * Returns an integer value savely without thrown exceptions.
     * @param configuration The {@link ILaunchConfiguration} to read from.
     * @param key The key to read.
     * @param defaultValue The default value to use.
     * @return The value of the key.
     */
    public static int getSaveInt(ILaunchConfiguration configuration, String key, int defaultValue) {
        try {
            return configuration != null ? configuration.getAttribute(key, defaultValue) : defaultValue;
        }
        catch (Exception e) {
            return defaultValue;
        }
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
     * @param file The {@link IFile} to launch.
     * @return The new created {@link ILaunchConfiguration}.
     * @throws CoreException Occurred Exception.
     */
    public static ILaunchConfiguration createConfiguration(IFile file) throws CoreException {
        ILaunchConfiguration config = null;
        ILaunchConfigurationWorkingCopy wc = null;
        ILaunchConfigurationType configType = getConfigurationType();
        String path = file.getFullPath().toString();
        String name = file.getName();
        wc = configType.newInstance(null, LaunchUtil.getLaunchManager().generateLaunchConfigurationName(name));
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_NEW_DEBUG_SESSION, false);
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_FILE_TO_LOAD, path);
        wc.setMappedResources(new IResource[] {file});
        config = wc.doSave();
        return config;
    }
    
    /**
     * Creates a new {@link ILaunchConfiguration}.
     * @param method The {@link IMethod} to launch.
     * @param methodStartPosition An optional start position to execute only parts of the method.
     * @param methodEndPosition An optional end position to execute only parts of the method.
     * @return The new created {@link ILaunchConfiguration}.
     * @throws CoreException Occurred Exception.
     */
    public static ILaunchConfiguration createConfiguration(IMethod method,
                                                           Position methodStartPosition,
                                                           Position methodEndPosition) throws CoreException {
        ILaunchConfiguration config = null;
        ILaunchConfigurationWorkingCopy wc = null;
        ILaunchConfigurationType configType = getConfigurationType();
        String typeLabel = KeySEDUtil.getTypeValue(method);
        String methodLabel = KeySEDUtil.getMethodValue(method);
        String name = typeLabel + "#" + methodLabel;
        if (methodStartPosition != null && methodEndPosition != null) {
           name += " from " + methodStartPosition.getLine() + ", " + methodStartPosition.getColumn() + " to " + methodEndPosition.getLine() + ", " + methodEndPosition.getColumn(); // : is not alowed as name
        }
        wc = configType.newInstance(null, LaunchUtil.getLaunchManager().generateLaunchConfigurationName(name));
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_NEW_DEBUG_SESSION, true);
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_PROJECT, KeySEDUtil.getProjectValue(method));
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_TYPE, typeLabel);
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD, methodLabel);
        wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_EXECUTE_METHOD_RANGE, methodStartPosition != null && methodEndPosition != null);
        if (methodStartPosition != null) {
           wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_LINE, methodStartPosition.getLine());
           wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_START_COLUMN, methodStartPosition.getColumn());
        }
        if (methodEndPosition != null) {
           wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_LINE, methodEndPosition.getLine());
           wc.setAttribute(KeySEDUtil.LAUNCH_CONFIGURATION_TYPE_ATTRIBUTE_METHOD_RANGE_END_COLUMN, methodEndPosition.getColumn());
        }
        wc.setMappedResources(new IResource[] {method.getUnderlyingResource()});
        config = wc.doSave();
        return config;
    }
    
    /**
     * Searches all {@link ILaunchConfiguration} that handles
     * the given {@link IMethod}.
     * @param method The {@link IMethod} for that {@link ILaunchConfiguration}s are required.
     * @param methodStartPosition An optional start position to execute only parts of the method.
     * @param methodEndPosition An optional end position to execute only parts of the method.
     * @return The found {@link ILaunchConfiguration}s.
     * @throws CoreException Occurred Exception.
     */
    public static List<ILaunchConfiguration> searchLaunchConfigurations(IFile file) throws CoreException {
        // Get parameters
        String path = file != null ? file.getFullPath().toString() : null;
        // Compare existing configurations to with the parameters.
        ILaunchConfiguration[] configs = DebugPlugin.getDefault().getLaunchManager().getLaunchConfigurations(getConfigurationType());
        List<ILaunchConfiguration> result = new ArrayList<ILaunchConfiguration>(configs.length);
        for (ILaunchConfiguration config : configs) {
            // Check method
            if (!isNewDebugSession(config) &&
                ObjectUtil.equals(path, getFileToLoadValue(config))) {
               result.add(config);
            }
        }
        return result;
    }
    
    /**
     * Searches all {@link ILaunchConfiguration} that handles
     * the given {@link IMethod}.
     * @param method The {@link IMethod} for that {@link ILaunchConfiguration}s are required.
     * @param methodStartPosition An optional start position to execute only parts of the method.
     * @param methodEndPosition An optional end position to execute only parts of the method.
     * @return The found {@link ILaunchConfiguration}s.
     * @throws CoreException Occurred Exception.
     */
    public static List<ILaunchConfiguration> searchLaunchConfigurations(IMethod method,
                                                                        Position methodStartPosition,
                                                                        Position methodEndPosition) throws CoreException {
        // Get parameters
        String projectLabel = getProjectValue(method);
        String typeLabel = getTypeValue(method);
        String methodLabel = getMethodValue(method);
        // Compare existing configurations to with the parameters.
        ILaunchConfiguration[] configs = DebugPlugin.getDefault().getLaunchManager().getLaunchConfigurations(getConfigurationType());
        List<ILaunchConfiguration> result = new ArrayList<ILaunchConfiguration>(configs.length);
        for (ILaunchConfiguration config : configs) {
            // Check method
            if (isNewDebugSession(config) &&
                ObjectUtil.equals(projectLabel, getProjectValue(config)) &&
                ObjectUtil.equals(typeLabel, getTypeValue(config)) &&
                ObjectUtil.equals(methodLabel, getMethodValue(config))) {
                // Check method body or method part definition
                if (methodStartPosition != null && methodEndPosition != null) {
                    if (isExecuteMethodRange(config) &&
                        methodStartPosition.getLine() == getMethodRangeStartLine(config) &&
                        methodStartPosition.getColumn() == getMethodRangeStartColumn(config) &&
                        methodEndPosition.getLine() == getMethodRangeEndLine(config) &&
                        methodEndPosition.getColumn() == getMethodRangeEndColumn(config)) {
                        result.add(config);
                    }
                }
                else {
                    if (!isExecuteMethodRange(config)) {
                        result.add(config);
                    }
                }
            }
        }
        return result;
    }

    /**
     * Searches a {@link FunctionalOperationContract} with the given name.
     * @param operationContracts The available {@link FunctionalOperationContract} to search in.
     * @param contractName The name of the {@link FunctionalOperationContract} to search.
     * @return The found {@link FunctionalOperationContract} or {@code null} if no one was found.
     */
    public static FunctionalOperationContract findContract(ImmutableSet<FunctionalOperationContract> operationContracts, 
                                                           final String contractName) {
        return CollectionUtil.search(operationContracts, new IFilter<FunctionalOperationContract>() {
            @Override
            public boolean select(FunctionalOperationContract element) {
                return element != null && ObjectUtil.equals(element.getName(), contractName);
            }
        });
    }

   /**
    * Prints the {@link ISEDDebugTarget} into the console via {@link System#out}.
    * @param target The {@link ISEDDebugTarget} to print.
    * @throws DebugException Occurred Exception.
    */
   public static void printDebugTarget(ISEDDebugTarget target) throws DebugException {
      if (target != null) {
         System.out.println(target + "    (" + target.getClass() + ")");
         for (ISEDThread thread : target.getSymbolicThreads()) {
            printDebugNode(thread, 1);
         }
      }
      else {
         System.out.println("Target is null.");
      }
   }

   /**
    * Prints the given {@link ISEDDebugNode} into the console via {@link System#out}.
    * @param node The {@link ISEDDebugNode} to print.
    * @param level The level.
    * @throws DebugException Occurred Exception.
    */
   public static void printDebugNode(ISEDDebugNode node, int level) throws DebugException {
      // Print level
      for (int i = 0; i < level; i++) {
         System.out.print("\t");
      }
      // Print node and children
      if (node != null) {
         System.out.println(node);
         for (ISEDDebugNode child : node.getChildren()) {
            printDebugNode(child, level + 1);
         }
      }
      else {
         System.out.println("Node is null");
      }
   }
   
   /**
    * Returns the selected element of view "Debug".
    * @return The selected element of view "Debug" or {@code null} if no one is selected or if the view is not available.
    */
   public static Object getSelectedDebugElement() {
      IRunnableWithResult<Object> run = new AbstractRunnableWithResult<Object>() {
         @Override
         public void run() {
            IViewPart view = WorkbenchUtil.findView(IDebugUIConstants.ID_DEBUG_VIEW);
            if (view instanceof IDebugView) {
               ISelection selection = ((IDebugView)view).getViewer().getSelection();
               setResult(SWTUtil.getFirstElement(selection));
            }
         }
      };
      Display.getDefault().syncExec(run);
      return run.getResult();
   }
}