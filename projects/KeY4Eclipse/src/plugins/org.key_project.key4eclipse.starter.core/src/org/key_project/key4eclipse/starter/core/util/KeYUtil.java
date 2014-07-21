/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

package org.key_project.key4eclipse.starter.core.util;

import java.awt.Component;
import java.io.ByteArrayInputStream;
import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.lang.reflect.InvocationTargetException;
import java.util.Arrays;
import java.util.Comparator;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import javax.swing.JOptionPane;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBuffer;
import org.eclipse.core.filebuffers.ITextFileBufferManager;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.ILocalVariable;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.ISourceRange;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaCore;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.IDocument;
import org.eclipse.ui.texteditor.AbstractTextEditor;
import org.key_project.key4eclipse.starter.core.job.AbstractKeYMainWindowJob;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.IOUtil;
import org.key_project.util.java.IOUtil.LineInformation;
import org.key_project.util.java.SwingUtil;
import org.key_project.util.java.thread.AbstractRunnableWithException;
import org.key_project.util.java.thread.AbstractRunnableWithResult;
import org.key_project.util.java.thread.IRunnableWithException;
import org.key_project.util.java.thread.IRunnableWithResult;
import org.key_project.util.jdt.JDTUtil;

import recoder.parser.JavaCharStream;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.PositionInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.DefaultProblemLoader;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.mgt.EnvNode;
import de.uka.ilkd.key.proof.mgt.TaskTreeModel;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
import de.uka.ilkd.key.proof_references.KeYTypeUtil;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.MiscTools;

/**
 * <p>
 * Provides static utility methods for the KeY eclipse integration.
 * </p>
 * <p>
 * <b>Attention: </b>
 * Byte code locations like JAR files are not supported. It is possible to
 * compute them but the used recorder in KeY is not able to parse them correctly!
 * </p>
 * <p>
 * <b>Attention: </b>
 * KeY supports at the moment no way to handle different source code locations.
 * For this reasons are Java projects with multiple source code locations
 * are not supported.
 * </p>
 * @author Martin Hentschel
 */
public final class KeYUtil {
    /**
     * The file extension for *.key files.
     */
    public static final String KEY_FILE_EXTENSION = "key";

    /**
     * The file extension for *.proof files.
     */
    public static final String PROOF_FILE_EXTENSION = "proof";
    
    /**
     * The used tab size in KeY's recorder component.
     */
    public static final int RECORDER_TAB_SIZE = 8;
    
    /**
     * Forbid instances.
     */
    private KeYUtil() {
    }
    
    /**
     * Checks if the given extension is supported by KeY.
     * @param extension The file extension to check.
     * @return {@code true} supported by KeY, {@code false} not supported by KeY.
     */
    public static boolean isFileExtensionSupported(String extension) {
        if (extension != null) {
            String lowerExtension = extension.toLowerCase();
            return KEY_FILE_EXTENSION.equals(lowerExtension) ||
                   PROOF_FILE_EXTENSION.equals(lowerExtension);
        }
        else {
            return false;
        }
    }
    
    /**
     * <p>
     * Executes {@link #openMainWindow()} asynchronous.
     * </p>
     * <p>
     * <b>Attention: </b> The asynchronous execution is required on MAC OS!
     * </p>
     * @throws InvocationTargetException Occurred Exception.
     * @throws InterruptedException Occurred Exception. 
     */
    public static void openMainWindowAsync() throws InterruptedException, InvocationTargetException {
        new AbstractKeYMainWindowJob("Starting KeY") {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
                try {
                    openMainWindow();
                    return Status.OK_STATUS;
                } 
                catch (Exception e) {
                    return LogUtil.getLogger().createErrorStatus(e);
                }
            }
        }.schedule();
    }

    /**
     * Opens the KeY main window via {@link Main#main(String[])}.
     * @throws InvocationTargetException Occurred Exception.
     * @throws InterruptedException Occurred Exception.
     */
    public static void openMainWindow() throws InterruptedException, InvocationTargetException {
        SwingUtil.invokeAndWait(new Runnable() {
            @Override
            public void run() {
                MainWindow.getInstance().setVisible(true);
            }
        });
    }
 
    /**
     * <p>
     * Executes {@link #load(IResource)} asynchronous.
     * </p>
     * <p>
     * <b>Attention: </b> The asynchronous execution is required on MAC OS!
     * </p>
     * @param locationToLoad The location to load.
     * @throws InvocationTargetException Occurred Exception.
     * @throws InterruptedException Occurred Exception.
     */
    public static void loadAsync(final IResource locationToLoad) throws InterruptedException, InvocationTargetException {
        new AbstractKeYMainWindowJob("Loading Project in KeY") {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
                try {
                    load(locationToLoad);
                    return Status.OK_STATUS;
                } 
                catch (Exception e) {
                    return LogUtil.getLogger().createErrorStatus(e);
                }
            }
        }.schedule();
    }
 
    /**
     * Opens the KeY main window and loads the given location.
     * If the location is already loaded the {@link ProofManagementDialog}
     * is shown again for this location.
     * @param locationToLoad The location to load.
     * @throws Exception Occurred Exception.
     */
    public static void load(IResource locationToLoad) throws Exception {
        if (locationToLoad != null) {
            final File location;
            final File bootClassPath;
            final List<File> classPaths;
            if (locationToLoad instanceof IFile) {
                location = ResourceUtil.getLocation(locationToLoad);
                bootClassPath = null;
                classPaths = null;
            }
            else {
                // Make sure that the location is contained in a Java project
                IProject project = locationToLoad.getProject();
                // Get local file for the eclipse resource
                location = getSourceLocation(project);
                // Get KeY project settings
                bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
                classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
            }
            Assert.isNotNull(location, "The resource \"" + locationToLoad + "\" is not local.");
            IRunnableWithException run = new AbstractRunnableWithException() {
                @Override
                public void run() {
                    try {
                        // Open main window
                        openMainWindow();
                        // Make sure that main window is available.
                        Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
                        // Check if environment is already loaded
                        InitConfig alreadyLoadedConfig = getInitConfig(location); 
                        if (alreadyLoadedConfig != null) {
                            // Open proof management dialog
                            ProofManagementDialog.showInstance(alreadyLoadedConfig);
                        }
                        else {
                            // Load local file
                            MainWindow.getInstance().loadProblem(location, classPaths, bootClassPath);
                        }
                    }
                    catch (Exception e) {
                        setException(e);
                    }
                }
            };
            SwingUtil.invokeAndWait(run);
            if (run.getException() != null) {
                throw run.getException();
            }
        }
    }
    
    /**
     * Returns an already loaded {@link InitConfig} for the given location.
     * @param location The given location.
     * @return The already loaded {@link InitConfig} or {@code null} if no one is loaded.
     * @throws InvocationTargetException Occurred Exception.
     * @throws InterruptedException Occurred Exception.
     */
    public static InitConfig getInitConfig(final File location) throws InterruptedException, InvocationTargetException {
        IRunnableWithResult<InitConfig> run = new AbstractRunnableWithResult<InitConfig>() {
            @Override
            public void run() {
                if (location != null) {
                    TaskTreeModel model = MainWindow.getInstance().getProofList().getModel();
                    InitConfig result = null;
                    int i = 0;
                    while (result == null && i < model.getChildCount(model.getRoot())) {
                        Object child = model.getChild(model.getRoot(), i);
                        if (child instanceof EnvNode) {
                            EnvNode envChild = (EnvNode)child;
                            String srcPath = envChild.getProofEnv().getJavaModel().getModelDir();
                            if (srcPath != null && location.equals(new File(srcPath))) {
                                result = envChild.getProofEnv().getInitConfigForEnvironment();
                            }
                        }
                        i++;
                    }
                    setResult(result);
                }
                else {
                    setResult(null);
                }
            }
        };
        SwingUtil.invokeAndWait(run);
        return run.getResult();
    }
    
    /**
     * <p>
     * Executes {@link #startProof(IMethod)} asynchronous.
     * </p>
     * <p>
     * <b>Attention: </b> The asynchronous execution is required on MAC OS!
     * </p>
     * @param method The {@link IMethod} to start proof for.
     * @throws Exception Occurred Exception.
     */
    public static void startProofAsync(final IMethod method) throws Exception {
        new AbstractKeYMainWindowJob("Starting Proof in KeY") {
            @Override
            protected IStatus run(IProgressMonitor monitor) {
                try {
                    startProof(method);
                    return Status.OK_STATUS;
                } 
                catch (Exception e) {
                    return LogUtil.getLogger().createErrorStatus(e);
                }
            }
        }.schedule();
    }
    
    /**
     * Returns the source location of the given {@link IProject}.
     * @param project The {@link IProject} to get its source location.
     * @return The source location.
     * @throws JavaModelException Occurred Exception if {@link IProject} is not supported.
     */
    public static File getSourceLocation(IProject project) throws JavaModelException {
       if (project != null) {
          if (JDTUtil.isJavaProject(project)) {
             List<File> sourcePaths = JDTUtil.getSourceLocations(project);
             if (1 == sourcePaths.size()) {
                return sourcePaths.get(0);
             }
             else {
                throw new JavaModelException(new CoreException(LogUtil.getLogger().createErrorStatus("Multiple source paths are not supported.")));
             }
          }
          else {
             throw new JavaModelException(new CoreException(LogUtil.getLogger().createErrorStatus("The project \"" + project.getName() + "\" is no Java project.")));
          }
       }
       else {
          throw new JavaModelException(new CoreException(LogUtil.getLogger().createErrorStatus("Project not defined.")));
       }
    }
    
    /**
     * Starts a proof for the given {@link IMethod}.
     * @param method The {@link IMethod} to start proof for.
     * @throws Exception Occurred Exception.
     */
    public static void startProof(final IMethod method) throws Exception {
        if (method != null) {
            // make sure that the method has a resource
            Assert.isNotNull(method.getResource(), "Method \"" + method + "\" is not part of a workspace resource.");
            // Make sure that the location is contained in a Java project
            IProject project = method.getResource().getProject();
            // Get local file for the eclipse resource
            final File location = getSourceLocation(project);
            // Get KeY project settings
            final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
            final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
            Assert.isNotNull(location, "The resource \"" + method.getResource() + "\" is not local.");
            // Open main window to avoid repaint bugs
            openMainWindow();
            // Load location and open proof management dialog
            IRunnableWithException run = new AbstractRunnableWithException() {
                @Override
                public void run() {
                    try {
                        // Make sure that main window is available.
                        Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
                        // Load location
                        InitConfig initConfig = internalLoad(null, location, classPaths, bootClassPath, true);
                        // Get method to proof in KeY
                        IProgramMethod pm = getProgramMethod(method, initConfig.getServices().getJavaInfo());
                        Assert.isNotNull(pm, "Can't find method \"" + method + "\" in KeY.");
                        // Start proof by showing the proof management dialog
                        ProofManagementDialog.showInstance(initConfig, pm.getContainerType(), pm);
                    }
                    catch (Exception e) {
                        setException(e);
                    }
                }
            };
            SwingUtil.invokeAndWait(run);
            if (run.getException() != null) {
                throw run.getException();
            }
        }
    }
    
    /**
     * Loads the given location in KeY and returns the opened {@link InitConfig}.
     * @param profile The {@link Profile} to use.
     * @param location The location to load.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param showKeYMainWindow Show KeY {@link MainWindow}? <b>Attention: </b> The {@link InitConfig} is not available in the proof tree, because no proof is started.
     * @return The opened {@link InitConfig}.
     * @throws Exception Occurred Exception.
     */
    private static InitConfig internalLoad(final Profile profile,
                                           final File location,
                                           final List<File> classPaths,
                                           final File bootClassPath,
                                           final boolean showKeYMainWindow) throws Exception {
        IRunnableWithResult<InitConfig> run = new AbstractRunnableWithResult<InitConfig>() {
            @Override
            public void run() {
                try {
                    MainWindow main = MainWindow.getInstance();
                    if (showKeYMainWindow) {
                       main.setVisible(true);
                    }
                    if (showKeYMainWindow && !main.isVisible()) {
                        main.setVisible(true);
                    }
                    // Check if location is already loaded
                    InitConfig initConfig = getInitConfig(location);
                    if (initConfig == null) {
                        // Load local file
                        DefaultProblemLoader loader = main.getUserInterface().load(profile, location, classPaths, bootClassPath);
                        initConfig = loader.getInitConfig();
                    }
                    setResult(initConfig);
                }
                catch (Exception e) {
                    setException(e);
                }
            }
        };
        SwingUtil.invokeAndWait(run);
        if (run.getException() != null) {
            throw run.getException();
        }
        return run.getResult();
    }
    
    /**
     * Returns the passed method in KeY representation.
     * @param method The method representation in JDT for that the KeY representation is needed.
     * @param javaInfo The {@link JavaInfo} of KeY to use.
     * @return The found method representation in KeY.
     * @throws ProofInputException Occurred Exception.
     */
    public static IProgramMethod getProgramMethod(IMethod method, 
                                                  JavaInfo javaInfo) throws ProofInputException {
        try {
            // Determine container type
            IType containerType = method.getDeclaringType();
            String containerTypeName = containerType.getFullyQualifiedName();
            containerTypeName = containerTypeName.replace('$', '.'); // Inner and anonymous classes are separated with '.' instead of '$' in KeY
            KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
            Assert.isNotNull(containerKJT, "Can't find type \"" + containerTypeName + "\" in KeY.\nIt can happen when Java packages are based on links in Eclipse.");
            // Determine parameter types
            ImmutableList<KeYJavaType> signature = getParameterKJTs(method, javaInfo);
            // Determine name
            String methodName = method.getElementName();
            // Ask javaInfo
            IProgramMethod result;
            if (method.isConstructor()) {
               result = javaInfo.getConstructor(containerKJT, signature);
            }
            else {
               result = javaInfo.getProgramMethod(containerKJT, methodName, signature, containerKJT);
            }
            if (result == null) {
                throw new ProofInputException("Error looking up method: " +
                                              "ProgramMethod not found: \""  +
                                              methodName +
                                              "\nsignature: " + signature + 
                                              "\ncontainer: " + containerType);
            }
            return result;
        }
        catch (JavaModelException e) {
            throw new ProofInputException(e);
        }
    }
    
    /**
     * Returns the parameter types of the passed method in KeY representation.
     * @param method The method representation in JDT for that the KeY class representations are required.
     * @param javaInfo The {@link JavaInfo} of KeY to use.
     * @return The found {@link KeYJavaType}.
     * @throws ProofInputException Occurred Exception.
     * @throws JavaModelException Occurred Exception.
     */
    public static ImmutableList<KeYJavaType> getParameterKJTs(IMethod method, JavaInfo javaInfo) throws ProofInputException, JavaModelException {
        ImmutableList<KeYJavaType> result = ImmutableSLList.<KeYJavaType>nil();
        IType declaringType         = method.getDeclaringType();
        ILocalVariable[] parameters = method.getParameters();
        for (ILocalVariable parameter : parameters) {
            String javaTypeName = JDTUtil.getQualifiedParameterType(declaringType, parameter);
            if(javaTypeName == null) {
                throw new ProofInputException("Error determining signature types: " + 
                                              "Could not resolve type " + 
                                              parameter + 
                                              "! This is probably a syntax problem, " + 
                                              " check your import statements.");
            }
            KeYJavaType kjt = javaInfo.getKeYJavaType(javaTypeName);
            result = result.append(kjt);
        }
        return result;
    }
    
    /**
     * Shows the exception to the error dialog to the user via Swing.
     * @param t The {@link Throwable} to show.
     */
    public static void showErrorInKey(Throwable t) {
        if (t != null) {
            Component parentComponent = null;
            if (MainWindow.hasInstance()) {
                parentComponent = MainWindow.getInstance();
            }
            JOptionPane.showMessageDialog(parentComponent, 
                                          t, 
                                          "Error", 
                                          JOptionPane.ERROR_MESSAGE);
        }
    }

    /**
     * Removes all proofs from the proof list of the given {@link MainWindow}.
     * @param main The {@link MainWindow} to remove all proofs from.
     */
    public static void clearProofList(MainWindow main) {
       TaskTreeModel model = main.getProofList().getModel();
       while (model.getChildCount(model.getRoot()) >= 1) {
          Object child = model.getChild(model.getRoot(), 0);
          if (child instanceof EnvNode) {
             EnvNode envChild = (EnvNode)child;
             for (Proof proof : envChild.allProofs()) {
                main.getUserInterface().removeProof(proof);
             }
             for (int j = 0; j < envChild.getChildCount(); j++) {
                Object envTaskChild = envChild.getChildAt(j);
                if (envTaskChild instanceof TaskTreeNode) {
                   TaskTreeNode ttn = (TaskTreeNode)envTaskChild;
                   for (Proof proof : ttn.allProofs()) {
                      main.getUserInterface().removeProof(proof);
                   }
                }
             }
          }
       }
    }
    
    /**
     * Checks if the proof list contains some entries.
     * @param main The {@link MainWindow} to check.
     * @return {@code true} proof list is empty, {@code false} proof list contains at least on entry.
     */
    public static boolean isProofListEmpty(MainWindow main) {
       TaskTreeModel model = main.getProofList().getModel();
       return model.getChildCount(model.getRoot()) == 0;
    }
    
    /**
     * Blocks the current {@link Thread} while the {@link MainWindow} is frozen.
     * @param main The {@link MainWindow} to wait for.
     */
    public static void waitWhileMainWindowIsFrozen(MainWindow main) {
        // Wait for interactive prover
        while (main.frozen) {
            try {
                Thread.sleep(250);
            }
            catch (InterruptedException e) {
                // Nothing to do
            }
        }
    }
    
    /**
     * Returns the name of the applied rule in the given {@link Node} of
     * the proof tree in KeY.
     * @param node The given {@link Node}.
     * @return The display name of the applied rule in the given {@link Node} or {@code null} if no one exists.
     */
    public static String getRuleDisplayName(Node node) {
       return MiscTools.getRuleDisplayName(node);
    }

    /**
     * Tries to close the given {@link Proof} in KeY with the automatic mode.
     * The current {@link Thread} is blocked until the automatic mode has finished.
     * The result dialog with the statistics is not shown to the user.
     * @param proof The {@link Proof} to close.
     */
    public static void runProofInAutomaticModeWithoutResultDialog(Proof proof) {
       runProofInAutomaticModeWithoutResultDialog(proof, proof.openEnabledGoals());
    }

    /**
     * Tries to close the given {@link Proof} in KeY with the automatic mode.
     * The current {@link Thread} is blocked until the automatic mode has finished.
     * The result dialog with the statistics is not shown to the user.
     * @param proof The {@link Proof} to close.
     * @param goals The {@link Goal}s to work with.
     */
    public static void runProofInAutomaticModeWithoutResultDialog(final Proof proof,
                                                                  final ImmutableList<Goal> goals) {
       try {
         runWithoutResultDialog(new IRunnableWithMainWindow() {
             @Override
             public void run(MainWindow main) {
                // Start interactive proof automatically
                main.getMediator().setProof(proof);
                main.getMediator().startAutoMode(goals);
                // Wait for interactive prover
                KeYUtil.waitWhileMainWindowIsFrozen(main);
             }
          });
       }
       catch (Exception e) {
          throw new RuntimeException(e); // Should never happen because run throws no exception
       }
    }
    
    /**
     * Disables the result dialog of KeY's MainWindow, 
     * executes the given {@link IRunnableWithMainWindow} and
     * finally enables the result dialog again. 
     * @param run The {@link IRunnableWithMainWindow} to execute.
     * @throws Exception Occurred Exception.
     */
    public static void runWithoutResultDialog(IRunnableWithMainWindow run) throws Exception {
       if (run != null) {
          // Make sure that main window is available.
          Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
          MainWindow main = MainWindow.getInstance();
          Assert.isNotNull(main, "KeY main window is not available.");
          // Run proof
          NotificationTask task = null;
          try {
             // Deactivate proof closed dialog
             task = main.getNotificationManager().getNotificationTask(NotificationEventID.PROOF_CLOSED);
             if (task != null) {
                main.getNotificationManager().removeNotificationTask(task);
             }
             // Execute runnable.
             run.run(main);
          }
          finally {
             if (task != null) {
                main.getNotificationManager().addNotificationTask(task);
             }
          }
       }
    }
    
    /**
     * Implementation provides some code which should be executed via
     * {@link KeYUtil#runWithoutResultDialog(IRunnableWithMainWindow)}.
     * @author Martin Hentschel
     */
    public static interface IRunnableWithMainWindow {
       /**
        * The code to execute.
        * @param main The {@link MainWindow} to use.
        * @throws Exception Occurred Exception.
        */
       public void run(MainWindow main) throws Exception;
    }

   /**
    * <p>
    * Normalizes the given column index computed by KeY's recorder component into
    * a normal column index in that each tab ({@code '\t'}) character has a fixed tab size 
    * of one which means that a tab is treated as a normal character.
    * </p>
    * <p>
    * KeY's recorder component has a default tab size of {@link #RECORDER_TAB_SIZE}.
    * But instead of using this fixed tab size the recorder component uses the following
    * simplified code to compute the column index:
    * <pre><code>
    * int column = 0;
    * for (char sign : signs) {
    *    switch (sign) {
    *        case '\t' : column += (tabSize - (column % tabSize));
    *                    break;
    *        default : column ++;
    *     }
    * }
    * </code></pre>
    * The class of recorder which does the mentioned computation is {@link JavaCharStream}.
    * </p>
    * @param column The column computed by KeY's recorder component.
    * @param tabIndices The indices of tab ({@code '\t'}) characters in the current line. They can be computed for instance via {@link IOUtil#computeLineInformation(File)}. 
    * @return The normalized column index in that each tab ({@code '\t'}) character has a fixed tab size of one which means that a tab is treated as a normal character.
    */   
   public static int normalizeRecorderColumn(int column, int[] tabIndices) {
      return normalizeRecorderColumn(column, RECORDER_TAB_SIZE, tabIndices);
   }
   
   /**
    * <p>
    * Normalizes the given column index computed by KeY's recorder component into
    * a normal column index in that each tab ({@code '\t'}) character has a fixed tab size 
    * of one which means that a tab is treated as a normal character.
    * </p>
    * <p>
    * KeY's recorder component has a default tab size of {@link #RECORDER_TAB_SIZE}.
    * But instead of using this fixed tab size the recorder component uses the following
    * simplified code to compute the column index:
    * <pre><code>
    * int column = 0;
    * for (char sign : signs) {
    *    switch (sign) {
    *        case '\t' : column += (tabSize - (column % tabSize));
    *                    break;
    *        default : column ++;
    *     }
    * }
    * </code></pre>
    * The class of recorder which does the mentioned computation is {@link JavaCharStream}.
    * </p>
    * @param column The column computed by KeY's recorder component.
    * @param tabSize The tab size to use.
    * @param tabIndices The indices of tab ({@code '\t'}) characters in the current line. They can be computed for instance via {@link IOUtil#computeLineInformation(File)}. 
    * @return The normalized column index in that each tab ({@code '\t'}) character has a fixed tab size of one which means that a tab is treated as a normal character.
    */
   public static int normalizeRecorderColumn(int column, int tabSize, int[] tabIndices) {
      if (column >= 0 && tabSize >= 2 && tabIndices != null) {
         int result = 0;
         int i = 0;
         int lastTab = -1;
         int tabOverhead = 0;
         while (i < tabIndices.length) {
            if (lastTab >= 0) {
               result += tabIndices[i] - lastTab;
            }
            else {
               result = tabIndices[i];
            }
            if (result < column) {
               tabOverhead += (tabSize - (result % tabSize) - 1);
               result += (tabSize - (result % tabSize) - 1);
            }
            lastTab = tabIndices[i];
            i++;
         }
         return column - tabOverhead;
      }
      else {
         return column;
      }
   }

   /**
    * <p>
    * Opens an {@link IDocument} for the source file defined by the given {@link IJavaElement}
    * and executes some code on it defined via the give {@link IRunnableWithDocument}.
    * </p>
    * <p>
    * If the {@link IDocument} is already opened its {@link IDocument} is used.
    * If it is not opened it is opened and closed after executing the {@link IRunnableWithDocument}.
    * </p>
    * @param element The {@link IJavaElement} to open its source file.
    * @param run The {@link IRunnableWithDocument} to execute on the opened {@link IDocument}.
    * @return {@code true} {@link IRunnableWithDocument} was executed, {@code false} {@link IRunnableWithDocument} was not executed.
    * @throws CoreException Occurred Exception.
    */

   public static boolean runOnDocument(IJavaElement element, IRunnableWithDocument run) throws CoreException {
      if (element != null) {
         return runOnDocument(element.getPath(), run);
      }
      else {
         return false;
      }
   }
   
   /**
    * <p>
    * Opens an {@link IDocument} for the file defined by the given {@link IPath}
    * and executes some code on it defined via the give {@link IRunnableWithDocument}.
    * </p>
    * <p>
    * If the {@link IDocument} is already opened its {@link IDocument} is used.
    * If it is not opened it is opened and closed after executing the {@link IRunnableWithDocument}.
    * </p>
    * @param location The {@link IPath} to open.
    * @param run The {@link IRunnableWithDocument} to execute on the opened {@link IDocument}.
    * @return {@code true} {@link IRunnableWithDocument} was executed, {@code false} {@link IRunnableWithDocument} was not executed.
    * @throws CoreException Occurred Exception.
    */
   public static boolean runOnDocument(IPath location, IRunnableWithDocument run) throws CoreException {
      if (location != null && run != null) {
         boolean closeRequired = false;
         ITextFileBufferManager bufferManager = FileBuffers.getTextFileBufferManager();
         try {
            ITextFileBuffer textFileBuffer = bufferManager.getTextFileBuffer(location, LocationKind.IFILE);
            if (textFileBuffer == null) {
               closeRequired = true;
               bufferManager.connect(location, LocationKind.IFILE, null);
               textFileBuffer = bufferManager.getTextFileBuffer(location, LocationKind.IFILE);
            }
            if (textFileBuffer != null) {
               IDocument document = textFileBuffer.getDocument();
               run.run(document);
               return true;
            }
            else {
               return false;
            }
         }
         finally {
            if (closeRequired && bufferManager != null) {
               bufferManager.disconnect(location, LocationKind.IFILE, null);
            }
         }
      }
      else {
         return false;
      }
   }
   
   /**
    * The method {@link #run(IDocument)} is executed via 
    * {@link KeYUtil#runOnDocument(IJavaElement, IRunnableWithDocument)} or
    * {@link KeYUtil#runOnDocument(IPath, IRunnableWithDocument)} and can
    * be used to do something with an opened {@link IDocument}.
    * @author Martin Hentschel
    */
   public static interface IRunnableWithDocument {
      /**
       * Does something with the given {@link IDocument}.
       * @param document The {@link IDocument} to work with.
       * @throws CoreException Occurred Exception.
       */
      public void run(IDocument document) throws CoreException;
   }
   
   /**
    * Converts the offset used in the source file of the given {@link IJavaElement}
    * into the cursor position shown to the user in the UI.
    * @param element The {@link IJavaElement} in which the offset is used.
    * @param offset The offset.
    * @return The cursor position shown to the user.
    * @throws CoreException Occurred Exception.
    */
   public static Position getCursorPositionForOffset(IJavaElement element, 
                                                     int offset) throws CoreException {
      if (element != null) {
         CursorPositionRunnable run = new CursorPositionRunnable(element, offset);
         runOnDocument(element, run);
         return run.getPosition();
      }
      else {
         return Position.UNDEFINED;
      }
   }
   
   /**
    * {@link IRunnableWithDocument} to compute the cursor position of
    * {@link KeYUtil#getCursorPositionForOffset(IJavaElement, int)}.
    * @author Martin Hentschel
    */
   private static class CursorPositionRunnable implements IRunnableWithDocument {
      /**
       * The {@link IJavaElement} in which the offset is used.
       */
      private IJavaElement element;
      
      /**
       * The offset.
       */
      private int offset;
      
      /**
       * The cursor position shown to the user.
       */
      private CursorPosition position;

      /**
       * Constructor.
       * @param element The {@link IJavaElement} in which the offset is used.
       * @param offset The offset.
       */
      public CursorPositionRunnable(IJavaElement element, int offset) {
         super();
         this.element = element;
         this.offset = offset;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void run(IDocument document) throws CoreException {
         try {
            int line = document.getLineOfOffset(offset);
            int lineOffset = document.getLineOffset(line);
            int tabWidth = JDTUtil.getTabWidth(element);
            int editorColumn = convertColumnToCursorColumn(document, lineOffset, offset, tabWidth);
            position = new CursorPosition(line + 1, editorColumn + 1);
         }
         catch (BadLocationException e) {
            throw new CoreException(LogUtil.getLogger().createErrorStatus("Can't compute cursor position for offset \"" + offset + "\" in \"" + element + "\".", e));
         }
      }

      /**
       * Returns the cursor position shown to the user.
       * @return The cursor position shown to the user.
       */
      public CursorPosition getPosition() {
         return position;
      }
   }
   
   /**
    * <p>
    * Computes for the offset used in the given {@link IDocument} with the
    * given tab width the column of the cursor position shown to the user.
    * </p>
    * <p>
    * The functionality was copied from {@link AbstractTextEditor#getCursorPosition()}.
    * </p>
    * @param document The {@link IDocument}.
    * @param lineOffset The line offset.
    * @param offset The offset.
    * @param tabWidth The tab width.
    * @return The cursor column.
    * @throws BadLocationException Occurred Exception.
    */
   private static int convertColumnToCursorColumn(IDocument document, 
                                                  int lineOffset, 
                                                  int offset, 
                                                  int tabWidth) throws BadLocationException {
      int column= 0;
      for (int i= lineOffset; i < offset; i++)
         if ('\t' == document.getChar(i))
            column += tabWidth - (tabWidth == 0 ? 0 : column % tabWidth);
         else
            column++;
      return column;
   }
   
   /**
    * An extension of KeY's recorder position which now represents
    * a cursor position shown to the user.
    * @author Martin Hentschel
    */
   public static class CursorPosition extends Position {
      /**
       * Constructor.
       * @param line The cursor line.
       * @param column The cursor column.
       */
      public CursorPosition(int line, int column) {
         super(line, column);
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public String toString() {
         StringBuffer buf = new StringBuffer();
         buf.append(getLine()).append(" : ").append(getColumn());
         return buf.toString();
      }
   }
   
   /**
    * Changes the cursor position if the tab width has changed.
    * @param document The {@link IDocument}.
    * @param position The old cursor position.
    * @param oldTabWidth The old tab width.
    * @param newTabWidth The new tab width.
    * @return The computed new cursor position with the new tab width.
    * @throws BadLocationException Occurred Exception.
    */
   public static Position changeCursorPositionTabWidth(IDocument document, 
                                                       Position position,
                                                       int oldTabWidth, 
                                                       int newTabWidth) throws BadLocationException {
      if (document != null && position != null) {
         int lineOffset = document.getLineOffset(position.getLine() - 1);
         int oldColumn = position.getColumn() - 1;
         int oldColumnRecomputed = 0;
         int newColumn = 0;
         int i = 0;
         while (oldColumnRecomputed < oldColumn) {
            if ('\t' == document.getChar(lineOffset + i)) {
               oldColumnRecomputed += oldTabWidth - (oldTabWidth == 0 ? 0 : oldColumnRecomputed % oldTabWidth);
               newColumn += newTabWidth - (newTabWidth == 0 ? 0 : newColumn % newTabWidth);
            }
            else {
               oldColumnRecomputed++;
               newColumn++;
            }
            i++;
         }
         return new CursorPosition(position.getLine(), newColumn + 1);
      }
      else {
         return Position.UNDEFINED;
      }
   }
   
   /**
    * Computes the offset for the given cursor position (line, column)
    * in the given {@link IDocument}.
    * @param document The {@link IDocument}.
    * @param cursorLine The line of the cursor.
    * @param cursorColumn The column of the cursor.
    * @param tabWidth The tab width.
    * @return The computed offset.
    * @throws BadLocationException Occurred Exception
    */
   public static int getOffsetForCursorPosition(IDocument document, 
                                                int cursorLine, 
                                                int cursorColumn, 
                                                int tabWidth) throws BadLocationException {
      if (document != null) {
         int lineOffset = document.getLineOffset(cursorLine - 1);
         int oldColumn = cursorColumn - 1;
         int oldColumnRecomputed = 0;
         int i = 0;
         while (oldColumnRecomputed < oldColumn) {
            if ('\t' == document.getChar(lineOffset + i)) {
               oldColumnRecomputed += tabWidth - (tabWidth == 0 ? 0 : oldColumnRecomputed % tabWidth);
            }
            else {
               oldColumnRecomputed++;
            }
            i++;
         }
         return lineOffset + i;
      }
      else {
         return -1;
      }
   }
   
   /**
    * Collects all {@link IMethod}s in the given {@link IResource}.
    * @param res - the given {@link IResource}
    * @return - the {@link LinkedList<IMethod>} with all {@link IMethod}s
    * @throws JavaModelException
    */
   public static LinkedList<IMethod> getResourceMethods(IResource res) throws JavaModelException{
      ICompilationUnit unit = (ICompilationUnit) JavaCore.create(res);
      LinkedList<IMethod> methods = new LinkedList<IMethod>();
      IType[] types = unit.getAllTypes();
      for(IType type : types){
         IMethod[] tmp = type.getMethods();
         for(IMethod method : tmp){
            methods.add(method);
         }
      }
      return methods;
   }
   
   /**
    * Collects all {@link IMethod}s in the given {@link IResource}.
    * @param res - the given {@link IResource}
    * @return - the {@link LinkedList<IMethod>} with all {@link IMethod}s
    * @throws JavaModelException
    */
   public static IType getType(IResource res) throws JavaModelException{
      ICompilationUnit unit = (ICompilationUnit) JavaCore.create(res);
      IType[] types = unit.getAllTypes();
      return types[0];
   }
   
   /**
    * Returns the lineNumber of the given {@link IMethod}.
    * @param method - the {@link IMethod} to use
    * @return the lineNumber of the {@link IMethod}
    * @throws CoreException
    */
   public static int getLineNumberOfMethod(IMethod method, int offset) throws CoreException {
      Position pos = KeYUtil.getCursorPositionForOffset(method, offset);
      return pos.getLine();
   }

   public static IMethod getContainingMethodForMethodStart(int charStart, IResource resource) throws CoreException {
      ICompilationUnit unit = (ICompilationUnit) JavaCore.create(resource);
      IJavaElement javaElement = unit.getElementAt(charStart);
      if(javaElement instanceof IMethod){
         return (IMethod) javaElement;
      }
      return null;
   } 
   
   public static LinkedList<IProgramMethod> getProgramMethods(LinkedList<IMethod> methods, JavaInfo javaInfo) throws ProofInputException{
      LinkedList<IProgramMethod> programMethods = new LinkedList<IProgramMethod>();
      for(IMethod method : methods){
         programMethods.add(getProgramMethod(method, javaInfo));
      }
      return programMethods;
   }
   

   public static IMethod getContainingMethod(int lineNumber, IResource resource) throws CoreException {
      LinkedList<IMethod>methods = getResourceMethods(resource);
      for(IMethod method : methods){
         int start = getLineNumberOfMethod(method, method.getSourceRange().getOffset());
         int end = getLineNumberOfMethod(method, method.getSourceRange().getOffset()+method.getSourceRange().getLength());
         if(lineNumber>start&&lineNumber<end){
            return method;
         }
      }
      return null;
   }
   
   /**
    * Computes the offset for the given cursor position (line, column)
    * in the source document of the given {@link IJavaElement}.
    * @param element The given {@link IJavaElement}.
    * @param cursorLine The line of the cursor.
    * @param cursorColumn The column of the cursor.
    * @return The computed offset.
    * @throws CoreException Occurred Exception
    */
   public static int getOffsetForCursorPosition(IJavaElement element, 
                                                int cursorLine, 
                                                int cursorColumn) throws CoreException {
      int tabWidth = JDTUtil.getTabWidth(element);
      OffsetForCursorPositionRunnableWithDocument run = new OffsetForCursorPositionRunnableWithDocument(cursorLine, cursorColumn, tabWidth);
      runOnDocument(element, run);
      return run.getOffset();
   }
   
   /**
    * Implementation of {@link IRunnableWithDocument} to compute the offset
    * of a given cursor position used by {@link KeYUtil#getOffsetForCursorPosition(IJavaElement, int, int)}.
    * @author Martin Hentschel
    */
   private static class OffsetForCursorPositionRunnableWithDocument implements IRunnableWithDocument {
      /**
       * The cursor line.
       */
      private int cursorLine;
      
      /**
       * The cursor column.
       */
      private int cursorColumn;
      
      /**
       * The tab width.
       */
      private int tabWidth;

      /**
       * The computed offset.
       */
      private int offset;
      
      /**
       * Constructor.
       * @param cursorLine The cursor line.
       * @param cursorColumn The cursor column.
       * @param tabWidth The tab width.
       */
      public OffsetForCursorPositionRunnableWithDocument(int cursorLine, 
                                                         int cursorColumn, 
                                                         int tabWidth) {
         super();
         this.cursorLine = cursorLine;
         this.cursorColumn = cursorColumn;
         this.tabWidth = tabWidth;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void run(IDocument document) throws CoreException {
         try {
            offset = getOffsetForCursorPosition(document, cursorLine, cursorColumn, tabWidth);
         }
         catch (BadLocationException e) {
            throw new CoreException(LogUtil.getLogger().createErrorStatus("Can't compute offset for cursor position " + cursorLine + " : " + cursorColumn + " with tab width " + tabWidth + ".", e));
         }
      }

      /**
       * The computed offset.
       * @return The computed offset.
       */
      public int getOffset() {
         return offset;
      }
   }

   /**
    * Converts the given {@link PositionInfo} into a {@link SourceLocation}.
    * This includes to convert position information defined via row and column
    * of the {@link PositionInfo} into character offset from file beginning
    * for the {@link SourceLocation}.
    * @param posInfo The {@link PositionInfo} to convert.
    * @return The created {@link PositionInfo}.
    */
   public static SourceLocation convertToSourceLocation(PositionInfo posInfo) {
      try {
         if (posInfo != null && posInfo != PositionInfo.UNDEFINED) {
            // Try to find the source file.
            String path = SymbolicExecutionUtil.getSourcePath(posInfo);
            File file = path != null ? new File(path) : null;
            // Check if a source file is available
            int charStart = -1;
            int charEnd = -1;
            int lineNumber = -1;
            if (file != null) {
               // Set source location
               LineInformation[] infos = IOUtil.computeLineInformation(file);
               if (posInfo.getStartPosition() != null) {
                  int line = posInfo.getStartPosition().getLine() - 1;
                  int column = posInfo.getStartPosition().getColumn();
                  if (line >= 0 && line < infos.length) {
                     LineInformation info = infos[line];
                     int offset = info.getOffset() + KeYUtil.normalizeRecorderColumn(column, info.getTabIndices());
                     charStart = offset;
                  }
               }
               if (posInfo.getEndPosition() != null) {
                  int line = posInfo.getEndPosition().getLine() - 1;
                  int column = posInfo.getEndPosition().getColumn();
                  if (line >= 0 && line < infos.length) {
                     LineInformation info = infos[line];
                     int offset = info.getOffset() + KeYUtil.normalizeRecorderColumn(column, info.getTabIndices());
                     charEnd = offset;
                  }
               }
               // Check if source start and end is defined.
               if (charStart < 0 || charEnd < 0) {
                  // Unset start and end indices
                  charStart = -1;
                  charEnd = -1;
                  // Try to set a line number as backup
                  if (posInfo.getEndPosition() != null) {
                     lineNumber = posInfo.getEndPosition().getLine();
                  }
               }
               return new SourceLocation(lineNumber, charStart, charEnd);
            }
            else {
               return SourceLocation.UNDEFINED;
            }
         }
         else {
            return SourceLocation.UNDEFINED;
         }
      }
      catch (IOException e) {
         LogUtil.getLogger().logError(e);
         return SourceLocation.UNDEFINED;
      }
   }

   
   /**
    * Represents a location in a source file.
    * @author Martin Hentschel
    */
   public static class SourceLocation {
      /**
       * Location which indicates that no location is defined.
       */
      public static final SourceLocation UNDEFINED = new SourceLocation(-1, -1, -1);
      
      /**
       * The line number to select.
       */
      private int lineNumber;
      
      /**
       * The index of the start character to select.
       */
      private int charStart;
      
      /**
       * The index of the end character to select.
       */
      private int charEnd;
      
      /**
       * Constructor.
       * @param lineNumber The line number to select.
       * @param charStart The index of the start character to select.
       * @param charEnd The index of the end character to select.
       */
      public SourceLocation(int lineNumber, int charStart, int charEnd) {
         super();
         this.lineNumber = lineNumber;
         this.charStart = charStart;
         this.charEnd = charEnd;
      }
      
      /**
       * Returns The line number to select.
       * @return The line number to select.
       */
      public int getLineNumber() {
         return lineNumber;
      }
      
      /**
       * Returns The index of the start character to select.
       * @return The index of the start character to select.
       */
      public int getCharStart() {
         return charStart;
      }
      
      /**
       * Returns The index of the end character to select.
       * @return The index of the end character to select.
       */
      public int getCharEnd() {
         return charEnd;
      }
   }
   
   public static void saveProof(Proof proof, IPath path) throws CoreException {
      Assert.isNotNull(proof);
      Assert.isNotNull(path);
      IFile file = ResourcesPlugin.getWorkspace().getRoot().getFile(path);
      saveProof(proof, file);
   }
   
   public static void saveProof(Proof proof, IFile file) throws CoreException {
      Assert.isNotNull(proof);
      Assert.isNotNull(file);
      try {
         File location = ResourceUtil.getLocation(file);
         // Create proof file content
         ProofSaver saver = new ProofSaver(proof, location.getAbsolutePath(), Main.INTERNAL_VERSION);
         ByteArrayOutputStream out = new ByteArrayOutputStream();
         String errorMessage = saver.save(out);
         if (errorMessage != null) {
            throw new CoreException(LogUtil.getLogger().createErrorStatus(errorMessage));
         }
         // Save proof file content
         if (file.exists()) {
            file.setContents(new ByteArrayInputStream(out.toByteArray()), true, true, null);
         }
         else {
            file.create(new ByteArrayInputStream(out.toByteArray()), true, null);
         }
      }
      catch (IOException e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e.getMessage(), e));
      }
   }
   
   /**
    * Returns for the given {@link SourceLocation} of a method in the given {@link IFile}
    * the {@link SourceLocation} of the method name if available or the initial location otherwise.
    * @param file The {@link IFile} which contains the method location.
    * @param methodLocation The location of the method in the given {@link IFile}.
    * @return The location of the method name or the initial location if not available.
    * @throws CoreException Occurred Exception.
    */
   public static SourceLocation updateToMethodNameLocation(IFile file, SourceLocation methodLocation) throws CoreException {
      try {
         if (file != null && methodLocation.getCharEnd() >= 0) {
            ICompilationUnit compilationUnit = null;
            IJavaElement element = JavaCore.create(file);
            if (element instanceof ICompilationUnit) {
               compilationUnit = (ICompilationUnit)element;
            }
            if (compilationUnit != null) {
               IMethod method = JDTUtil.findJDTMethod(compilationUnit, methodLocation.getCharEnd());
               if (method != null) {
                  ISourceRange range = method.getNameRange();
                  Position cursorStartPosition = getCursorPositionForOffset(element, range.getOffset()); 
                  methodLocation = new SourceLocation(cursorStartPosition != null ? cursorStartPosition.getLine() : -1, 
                                                      range.getOffset(), 
                                                      range.getOffset() + range.getLength());
               }
            }
         }
         return methodLocation;
      }
      catch (IOException e) {
         throw new CoreException(LogUtil.getLogger().createErrorStatus(e));
      }
   }
   
   /**
    * Filters the given {@link Set} of {@link KeYJavaType}s and sorts them.
    * @param kjts - the {@link KeYJavaType}s to filter and sort
    * @return the filtered and sorted {@link KeYJavaType[]}
    */
   public static KeYJavaType[] sortKeYJavaTypes(Set<KeYJavaType> kjts){ // TODO: Move to KeYUtil.sortKeYJavaTypes(Set<KeYJavaType>)
      Iterator<KeYJavaType> it = kjts.iterator();
      while (it.hasNext()) {
         KeYJavaType kjt = it.next();
         if (!(kjt.getJavaType() instanceof ClassDeclaration || 
               kjt.getJavaType() instanceof InterfaceDeclaration) || 
               KeYTypeUtil.isLibraryClass(kjt)) {
            it.remove();
         }
      }
      KeYJavaType[] kjtsarr = kjts.toArray(new KeYJavaType[kjts.size()]);
      Arrays.sort(kjtsarr, new Comparator<KeYJavaType>() {
         public int compare(KeYJavaType o1, KeYJavaType o2) {
            return o1.getFullName().compareTo(o2.getFullName());
         }
      });
      return kjtsarr;
   }
}