package org.key_project.key4eclipse.util.key;

import java.awt.Component;
import java.io.File;
import java.lang.reflect.InvocationTargetException;
import java.util.List;

import javax.swing.JOptionPane;

import org.eclipse.core.resources.IResource;
import org.eclipse.core.runtime.Assert;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.IStatus;
import org.eclipse.core.runtime.Status;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.core.Signature;
import org.key_project.key4eclipse.util.Activator;
import org.key_project.key4eclipse.util.eclipse.Logger;
import org.key_project.key4eclipse.util.eclipse.job.AbstractKeYMainWindowJob;
import org.key_project.key4eclipse.util.java.SwingUtil;
import org.key_project.key4eclipse.util.java.thread.AbstractRunnableWithException;
import org.key_project.key4eclipse.util.java.thread.IRunnableWithException;
import org.key_project.key4eclipse.util.jdt.JDTUtil;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofManagementDialog;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.proof.ProblemLoader;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.EnvInput;
import de.uka.ilkd.key.proof.mgt.EnvNode;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.proof.mgt.TaskTreeModel;
import de.uka.ilkd.key.proof.mgt.TaskTreeNode;

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
// TODO: Change path to config files via PathConfig
public final class KeYUtil {
    /**
     * Forbid instances.
     */
    private KeYUtil() {
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
                    return new Logger(Activator.getDefault(), Activator.PLUGIN_ID).createErrorStatus(e);
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
                Main.main(new String[] {});
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
                    return new Logger(Activator.getDefault(), Activator.PLUGIN_ID).createErrorStatus(e);
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
            // Make sure that the location is contained in a Java project
            Assert.isTrue(JDTUtil.isJavaProject(locationToLoad.getProject()), "The project \"" + locationToLoad.getProject() + "\" is no Java project.");
            // Get source paths from class path
            List<File> sourcePaths = JDTUtil.getSourceLocations(locationToLoad.getProject());
            Assert.isTrue(1 == sourcePaths.size(), "Multiple source paths are not supported.");
            // Get local file for the eclipse resource
            final File location = sourcePaths.get(0);
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
                            MainWindow.getInstance().loadProblem(location);
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
     */
    public static InitConfig getInitConfig(File location) {
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
            return result;
        }
        else {
            return null;
        }
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
                    return new Logger(Activator.getDefault(), Activator.PLUGIN_ID).createErrorStatus(e);
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
            Assert.isTrue(JDTUtil.isJavaProject(method.getResource().getProject()), " The project \"" + method.getResource().getProject() + "\" is no Java project.");
            // Get source paths from class path
            List<File> sourcePaths = JDTUtil.getSourceLocations(method.getResource().getProject());
            Assert.isTrue(1 == sourcePaths.size(), "Multiple source paths are not supported.");
            // Get local file for the eclipse resource
            final File location = sourcePaths.get(0);
            Assert.isNotNull(location, "The resource \"" + method.getResource() + "\" is not local.");
            IRunnableWithException run = new AbstractRunnableWithException() {
                @Override
                public void run() {
                    try {
                        // Open main window
                        openMainWindow();
                        // Make sure that main window is available.
                        Assert.isTrue(MainWindow.hasInstance(), "KeY main window is not available.");
                        // Check if location is already loaded
                        InitConfig initConfig = getInitConfig(location);
                        if (initConfig == null) {
                            // Load local file
                            MainWindow main = MainWindow.getInstance();
                            ProblemLoader loader = new ProblemLoader(location, main);
                            main.getRecentFiles().addRecentFile(location.getAbsolutePath());
                            EnvInput envInput = loader.createEnvInput(location);
                            ProblemInitializer init = main.createProblemInitializer();
                            initConfig = init.prepare(envInput);
                        }
                        // Get method to proof in KeY
                        ProgramMethod pm = getProgramMethod(method, initConfig.getServices().getJavaInfo());
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
            // Determine name ("<init>" for constructors)
            String methodName = method.isConstructor() ? "<init>" : method.getElementName();
            // Ask javaInfo
            ProgramMethod result = javaInfo.getProgramMethod(containerKJT, methodName, signature, containerKJT);
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
     */
    public static ImmutableList<KeYJavaType> getParameterKJTs(IMethod method, JavaInfo javaInfo) throws ProofInputException {
        ImmutableList<KeYJavaType> result = ImmutableSLList.<KeYJavaType>nil();
        IType declaringType         = method.getDeclaringType();
        String[] parameterTypeNames = method.getParameterTypes();
        for(int i = 0; i < parameterTypeNames.length; i++) {
            String javaTypeName = determineJavaType(parameterTypeNames[i], declaringType);

            if(javaTypeName == null) {
                throw new ProofInputException("Error determining signature types: " + 
                                              "Could not resolve type " + 
                                              parameterTypeNames[i] + 
                                              "! This is probably a syntax problem, " + 
                                              " check your import statements.");
            }
            KeYJavaType kjt = javaInfo.getKeYJavaTypeByClassName(javaTypeName);
            result = result.append(kjt);
        }
        return result;
    }
    
    /**
     * Computes the name of the java type.
     * @param eclipseSignature The signature in eclipse.
     * @param surroundingType The parent type.
     * @return The name of the java type.
     * @throws ProofInputException Occurred Exception.
     */
    public static String determineJavaType(String eclipseSignature, IType surroundingType) throws ProofInputException {
        try {
            switch(eclipseSignature.charAt(0)) {

            case Signature.C_ARRAY: // this parameter is an array
                int depth = Signature.getArrayCount(eclipseSignature);
                StringBuffer type = new StringBuffer(determineJavaType(Signature.getElementType(eclipseSignature), surroundingType));
                // array type is <element type> ([])+, now create the []s
                for (int i = 0; i < depth; i++) {
                    type.append('['); type.append(']');
                    // this is probably much faster, than handling String-objects ?!                
                }
                return type.toString();
            // primitive types:
            case Signature.C_BOOLEAN:
                return "boolean";

            case Signature.C_BYTE:
                return "byte";

            case Signature.C_CHAR:
                return "char";

            case Signature.C_DOUBLE:
                return "double";

            case Signature.C_FLOAT:
                return "float";

            case Signature.C_INT:
                return "int";

            case Signature.C_LONG:
                return "long";

            case Signature.C_SHORT:
                return "short";

            // arbitrary types with fully-qualified name
            case Signature.C_RESOLVED:
                return eclipseSignature.substring(1, eclipseSignature.length() - 1);
                // eclipse input is "Lpackage.Type;", so
                // cut off the first and last character

            // arbitrary types with unresolved names
            case Signature.C_UNRESOLVED:
                String unqualifiedTypeName = eclipseSignature.substring(1, eclipseSignature.length() - 1);
                String[][] resolvedTypes = surroundingType.resolveType(unqualifiedTypeName);                                    
                if (resolvedTypes != null && resolvedTypes.length > 0) {
                    return (resolvedTypes[0][0].equals("") ? "" : resolvedTypes[0][0] + ".") + resolvedTypes[0][1];
                } 
                else {
                    return null;
                }
            default:
                throw new ProofInputException("Not supported Eclipse Signature type " + eclipseSignature + ".");
            }
        }
        catch (JavaModelException e) {
            throw new ProofInputException(e);
        }
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
}
