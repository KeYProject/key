package org.key_project.key4eclipse.starter.core.util;

import java.awt.Component;
import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;

import javax.swing.JOptionPane;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.ILocalVariable;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.key_project.key4eclipse.starter.core.job.AbstractKeYMainWindowJob;
import org.key_project.key4eclipse.starter.core.property.KeYResourceProperties;
import org.key_project.util.eclipse.ResourceUtil;
import org.key_project.util.java.ArrayUtil;
import org.key_project.util.java.IOUtil;
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
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.gui.notification.NotificationEventID;
import de.uka.ilkd.key.gui.notification.NotificationTask;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.mgt.EnvNode;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.TaskTreeModel;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;
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
     * Key for the choice option "runtimeExceptions".
     */
    public static final String CHOICE_SETTING_RUNTIME_EXCEPTIONS = "runtimeExceptions";
   
    /**
     * Value in choice option "runtimeExceptions" to ban exceptions.
     */
    public static final String CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_BAN = "runtimeExceptions:ban";
    
    /**
     * Value in choice option "runtimeExceptions" to allow exceptions.
     */
    public static final String CHOICE_SETTING_RUNTIME_EXCEPTIONS_VALUE_ALLOW = "runtimeExceptions:allow";
   
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
                if (!MainWindow.hasInstance()) {
                   MainWindow.createInstance(Main.getMainWindowTitle());
                }
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
                Assert.isTrue(JDTUtil.isJavaProject(locationToLoad.getProject()), "The project \"" + project + "\" is no Java project.");
                // Get source paths from class path
                List<File> sourcePaths = JDTUtil.getSourceLocations(project);
                Assert.isTrue(1 == sourcePaths.size(), "Multiple source paths are not supported.");
                // Get KeY project settings
                bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
                classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
                // Get local file for the eclipse resource
                location = sourcePaths.get(0);
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
                            ProofManagementDialog.showInstance(MainWindow.getInstance().getMediator(), alreadyLoadedConfig);
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
                                result = envChild.getProofEnv().getInitConfig();
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
            Assert.isTrue(JDTUtil.isJavaProject(project), " The project \"" + project + "\" is no Java project.");
            // Get source paths from class path
            List<File> sourcePaths = JDTUtil.getSourceLocations(project);
            Assert.isTrue(1 == sourcePaths.size(), "Multiple source paths are not supported.");
            // Get KeY project settings
            final File bootClassPath = KeYResourceProperties.getKeYBootClassPathLocation(project);
            final List<File> classPaths = KeYResourceProperties.getKeYClassPathEntries(project);
            // Get local file for the eclipse resource
            final File location = sourcePaths.get(0);
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
                        InitConfig initConfig = internalLoad(location, classPaths, bootClassPath, true);
                        // Get method to proof in KeY
                        ProgramMethod pm = getProgramMethod(method, initConfig.getServices().getJavaInfo());
                        Assert.isNotNull(pm, "Can't find method \"" + method + "\" in KeY.");
                        // Start proof by showing the proof management dialog
                        ProofManagementDialog.showInstance(MainWindow.getInstance().getMediator(), initConfig, pm.getContainerType(), pm);
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
     * @param location The location to load.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param showKeYMainWindow Show KeY {@link MainWindow}? <b>Attention: </b> The {@link InitConfig} is not available in the proof tree, because no proof is started.
     * @return The opened {@link InitConfig}.
     * @throws Exception Occurred Exception.
     */
    public static InitConfig internalLoad(final File location,
                                          final List<File> classPaths,
                                          final File bootClassPath,
                                          final boolean showKeYMainWindow) throws Exception {
        IRunnableWithResult<InitConfig> run = new AbstractRunnableWithResult<InitConfig>() {
            @Override
            public void run() {
                try {
                    if (!MainWindow.hasInstance()) {
                        MainWindow.createInstance(Main.getMainWindowTitle());
                    }
                    MainWindow main = MainWindow.getInstance(showKeYMainWindow);
                    if (showKeYMainWindow && !main.isVisible()) {
                        main.setVisible(true);
                    }
                    // Check if location is already loaded
                    InitConfig initConfig = getInitConfig(location);
                    if (initConfig == null) {
                        // Load local file
                        ProblemLoader loader = new ProblemLoader(location, main.getMediator());
                        main.getRecentFiles().addRecentFile(location.getAbsolutePath());
                        EnvInput envInput = loader.createEnvInput(location, classPaths, bootClassPath);
                        ProblemInitializer init = main.getUserInterface().createProblemInitializer();
                        initConfig = init.prepare(envInput);
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
    public static ProgramMethod getProgramMethod(IMethod method, 
                                                 JavaInfo javaInfo) throws ProofInputException {
        try {
            // Determine container type
            IType containerType = method.getDeclaringType();
            String containerTypeName = containerType.getFullyQualifiedName();
            KeYJavaType containerKJT = javaInfo.getTypeByClassName(containerTypeName);
            Assert.isNotNull(containerKJT, "Can't find type \"" + containerTypeName + "\" in KeY.\nIt can happen when Java packages are based on links in Eclipse.");
            // Determine parameter types
            ImmutableList<KeYJavaType> signature = getParameterKJTs(method, javaInfo);
            // Determine name
            String methodName = method.getElementName();
            // Ask javaInfo
            ProgramMethod result;
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
            KeYJavaType kjt = javaInfo.getKeYJavaTypeByClassName(javaTypeName);
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
             for (int j = 0; j < envChild.getChildCount(); j++) {
                Object envTaskChild = envChild.getChildAt(j);
                if (envTaskChild instanceof TaskTreeNode) {
                   main.getProofList().removeTaskWithoutInteraction((TaskTreeNode)envTaskChild);
                }
             }
          }
       }
    }
    
    /**
     * Removes the whole {@link ProofEnvironment} with all contained proofs
     * from the proof list.
     * @param main The {@link MainWindow} to handle.
     * @param env The {@link ProofEnvironment} to remove.
     */
    public static void removeFromProofList(MainWindow main, ProofEnvironment env) {
       TaskTreeModel model = main.getProofList().getModel();
       EnvNode envNode = null;
       for (int i = 0; i < model.getChildCount(model.getRoot()); i++) {
          Object child = model.getChild(model.getRoot(), i);
          if (child instanceof EnvNode) {
             EnvNode envChild = (EnvNode)child;
             if (env != null ? env.equals(envChild.getProofEnv()) : envChild.getProofEnv() == null) {
                envNode = envChild;
             }
          }
       }
       if (envNode != null) {
          for (int i = 0; i < envNode.getChildCount(); i++) {
             Object child = envNode.getChildAt(i);
             if (child instanceof TaskTreeNode) {
                main.getProofList().removeTaskWithoutInteraction((TaskTreeNode)child);
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
          // Start interactive proof automatically
          main.getMediator().setProof(proof);
          main.getMediator().startAutoMode(proof.openEnabledGoals());
          // Wait for interactive prover
          KeYUtil.waitWhileMainWindowIsFrozen(main);
       }
       finally {
          if (task != null) {
             main.getNotificationManager().addNotificationTask(task);
          }
       }
    }

   /**
    * Returns the default choice value.
    * <b>Attention: </b> This method returns {@code null} if it is called before
    * a proof is instantiated the first time. It can be checked via
    * {@link #isChoiceSettingInitialised()}.
    * @param key The choice key.
    * @return The choice value.
    */
   public static String getChoiceSetting(String key) {
      Map<String, String> settings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
      return settings.get(key);
   }
   
   /**
    * Sets the default choice value.
    * <b>Attention: </b> Settings should not be changed before the first proof
    * is instantiated in KeY. Otherwise the default settings are not loaded.
    * If default settings are defined can be checked via {@link #isChoiceSettingInitialised()}.
    * @param key The choice key to modify.
    * @param value The new choice value to set.
    */
   public static void setChoiceSetting(String key, String value) {
      HashMap<String, String> settings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices();
      HashMap<String, String> clone = new HashMap<String, String>();
      clone.putAll(settings);
      clone.put(key, value);
      ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().setDefaultChoices(clone);
   }

   /**
    * Checks if the choice settings are initialized.
    * @return {@code true} settings are initialized, {@code false} settings are not initialized.
    */
   public static boolean isChoiceSettingInitialised() {
      return !ProofSettings.DEFAULT_SETTINGS.getChoiceSettings().getDefaultChoices().isEmpty();
   }   
   
   /**
    * Checks if the {@link Proof} exists in the user interface.
    * @param proof The {@link Proof} to check.
    * @return {@code true} = in UI, {@code false} = not in UI.
    */
   public static boolean isProofInUI(Proof proof) {
      boolean inUI = false;
      if (proof != null) {
         Set<ProofAggregate> proofAggregates = proof.env().getProofs();
         Iterator<ProofAggregate> iter = proofAggregates.iterator();
         while (!inUI && iter.hasNext()) {
            ProofAggregate next = iter.next();
            inUI = ArrayUtil.contains(next.getProofs(), proof);
         }
      }
      return inUI;
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
}
