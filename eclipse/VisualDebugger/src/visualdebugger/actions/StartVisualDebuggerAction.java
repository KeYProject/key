package visualdebugger.actions;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.util.*;

import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.*;
import org.eclipse.jdt.core.dom.*;
import org.eclipse.jface.action.IAction;
import org.eclipse.jface.dialogs.MessageDialog;
import org.eclipse.jface.text.BadLocationException;
import org.eclipse.jface.text.Document;
import org.eclipse.jface.viewers.ISelection;
import org.eclipse.jface.viewers.StructuredSelection;
import org.eclipse.jface.window.Window;
import org.eclipse.text.edits.MalformedTreeException;
import org.eclipse.text.edits.TextEdit;
import org.eclipse.text.edits.UndoEdit;
import org.eclipse.ui.IActionDelegate;
import org.eclipse.ui.IObjectActionDelegate;
import org.eclipse.ui.IWorkbenchPart;
import org.eclipse.ui.PlatformUI;

import visualdebugger.views.InsertSepVisitor;
import de.uka.ilkd.key.casetool.eclipse.EclipseSignaturesHelper;
import de.uka.ilkd.key.casetool.eclipse.MethodPOSelectionDialog;
import de.uka.ilkd.key.collection.ListOfString;
import de.uka.ilkd.key.collection.SLListOfString;
import de.uka.ilkd.key.gui.JMLEclipseAdapter;
import de.uka.ilkd.key.gui.JMLPOAndSpecProvider;
import de.uka.ilkd.key.gui.Main;
import de.uka.ilkd.key.jml.JMLMethodSpec;
import de.uka.ilkd.key.jml.JMLSpec;
import de.uka.ilkd.key.proof.init.*;
import de.uka.ilkd.key.util.ExceptionHandlerException;
import de.uka.ilkd.key.visualdebugger.DebuggerEvent;
import de.uka.ilkd.key.visualdebugger.VisualDebugger;

public class StartVisualDebuggerAction implements IObjectActionDelegate {

    public static boolean allInvariants = false;

    // public static boolean allInvariants=false;

    protected static final int PROJECT_ALREADY_OPEN = 1;

    protected static final int PROJECT_LOAD_CANCELED = 3;

    protected static final int PROJECT_LOAD_FAILED = 4;

    protected static final int PROJECT_LOAD_SUCESSFUL = 2;

    public static void deleteTree(File path) {

        final File[] files = path.listFiles();
        for (int i = 0; i < files.length; i++) {
            if (files[i].isDirectory())
                deleteTree(files[i]);
            files[i].delete();
        }
        path.delete();
    }

    public static void delTemporaryDirectory() {
        File dir = new File(VisualDebugger.tempDir);
        StartVisualDebuggerAction.deleteTree(dir);
        if (!dir.exists())
            dir.mkdirs();

    }

    private CompilationUnit debugCU;

    // quick-and-dirty for syncExec(dialog.open()) in swt thread
    MethodPOSelectionDialog dialog;

    boolean nokey = false;

    ISelection selection;

    int state;

    HashSet types = new HashSet();

    /**
     * Constructor for Action1.
     */
    public StartVisualDebuggerAction() {
        super();
    }

    protected synchronized int assertProjectParsed(IProject project,
            boolean jmlBrowserIntended) {

        // project's java model has not been loaded into KeY yet, do this
        // now

        final String inputName = "visualDebugger-project_" + project.getName();
        final File location = new File(VisualDebugger.tempDir);

        if (!location.exists()) {
            location.mkdirs();
        }

        Main main = Main.getInstance(false);

        JavaInput input;

        if (jmlBrowserIntended) {

            input = new JavaInputWithJMLSpecBrowser(inputName, location, false,
                    main.getProgressMonitor());

        } else {
            input = new JavaInput(inputName, location, main
                    .getProgressMonitor());
        }

        ProblemInitializer problemInit = new ProblemInitializer(main);

        String error = "Prover init for " + location + " failed.";
        try {
            problemInit.startProver(input, input);
            error = "";
        } catch (ProofInputException pie) {
            error = pie.getMessage();            
        } catch (ExceptionHandlerException ehe) {
            error =  ehe.getCause() == null ? ehe.getMessage() : 
                ehe.getCause().getMessage();
        }

        if (error.length() == 0) {
            return PROJECT_LOAD_SUCESSFUL;
        } else {
            MessageDialog.openError(PlatformUI.getWorkbench()
                    .getActiveWorkbenchWindow().getShell(),
                    "Error loading java model into KeY prover",
                    "While loading this project, the following error"
                            + " occured:\n" + error);
            return PROJECT_LOAD_FAILED;
        }

    }

    /**
     * creates class <tt>Debug</tt> implementing the <tt>sep</tt> methods
     * representing breakpoints.
     * 
     * @param ast
     *                the AST with the environment where to insert the class
     * @return the compilation unit containing the created class
     */
    private CompilationUnit createDebuggerClass(AST ast) {
        CompilationUnit unit = ast.newCompilationUnit();

        PackageDeclaration packageDeclaration = ast.newPackageDeclaration();
        packageDeclaration.setName(ast
                .newSimpleName(VisualDebugger.debugPackage));
        unit.setPackage(packageDeclaration);
        ImportDeclaration importDeclaration = ast.newImportDeclaration();
        TypeDeclaration type = ast.newTypeDeclaration();
        type.setInterface(false);
        Modifier mf = ast.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD);

        type.modifiers().add(mf);

        type.setName(ast.newSimpleName(VisualDebugger.debugClass));

        unit.types().add(type);

        return unit;
    }

    private JMLMethodSpec getMethodSpec(Vector methodSpecs) {
        for (Iterator it = methodSpecs.iterator(); it.hasNext();) {
            Object next = it.next();
            if (next instanceof JMLMethodSpec) {
                return (JMLMethodSpec) next;
            }

        }
        // TODO Auto-generated method stub
        return null;
    }

    private MethodDeclaration getSepMethodDeclaration(AST ast) {

        MethodDeclaration methodDeclaration = ast.newMethodDeclaration();
        methodDeclaration.setConstructor(false);
        Modifier mf = ast.newModifier(Modifier.ModifierKeyword.STATIC_KEYWORD);
        methodDeclaration.modifiers().add(mf);

        mf = ast.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD);
        methodDeclaration.modifiers().add(mf);

        methodDeclaration.setName(ast.newSimpleName("sep"));
        methodDeclaration.setReturnType2(ast
                .newPrimitiveType(PrimitiveType.VOID));
        SingleVariableDeclaration variableDeclaration = ast
                .newSingleVariableDeclaration();

        variableDeclaration.setType(ast.newPrimitiveType(PrimitiveType.INT));
        variableDeclaration.setName(ast.newSimpleName("id"));
        methodDeclaration.parameters().add(variableDeclaration);
        org.eclipse.jdt.core.dom.Block block = ast.newBlock();
        methodDeclaration.setBody(block);
        return methodDeclaration;
    }

    private MethodDeclaration getSepMethodDeclaration(AST ast, Type type) {

        MethodDeclaration methodDeclaration = ast.newMethodDeclaration();
        methodDeclaration.setConstructor(false);
        Modifier mf = ast.newModifier(Modifier.ModifierKeyword.STATIC_KEYWORD);
        methodDeclaration.modifiers().add(mf);

        mf = ast.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD);
        methodDeclaration.modifiers().add(mf);

        methodDeclaration.setName(ast.newSimpleName(VisualDebugger.sepName));

        methodDeclaration.setReturnType2(type);

        SingleVariableDeclaration variableDeclaration = ast
                .newSingleVariableDeclaration();

        variableDeclaration.setType(ast.newPrimitiveType(PrimitiveType.INT));
        variableDeclaration.setName(ast.newSimpleName("id"));

        SingleVariableDeclaration variableDeclaration2 = ast
                .newSingleVariableDeclaration();

        variableDeclaration2.setType((Type) ASTNode.copySubtree(ast, type));
        variableDeclaration2.setName(ast.newSimpleName("expr"));

        methodDeclaration.parameters().add(variableDeclaration);
        methodDeclaration.parameters().add(variableDeclaration2);

        org.eclipse.jdt.core.dom.Block block = ast.newBlock();
        ReturnStatement ret = ast.newReturnStatement();
        ret.setExpression(ast.newSimpleName("expr"));
        block.statements().add(ret);

        methodDeclaration.setBody(block);
        // System.out.println(methodDeclaration);
        return methodDeclaration;
    }

    private MethodDeclaration getSepMethodDeclarationDEPRECATED(AST ast,
            ITypeBinding type) {

        MethodDeclaration methodDeclaration = ast.newMethodDeclaration();
        methodDeclaration.setConstructor(false);
        Modifier mf = ast.newModifier(Modifier.ModifierKeyword.STATIC_KEYWORD);
        methodDeclaration.modifiers().add(mf);

        mf = ast.newModifier(Modifier.ModifierKeyword.PUBLIC_KEYWORD);
        methodDeclaration.modifiers().add(mf);

        methodDeclaration.setName(ast.newSimpleName("sep"));

        SimpleType loggerType = ast.newSimpleType(ast.newName(type
                .getQualifiedName()));

        methodDeclaration.setReturnType2(loggerType);

        SingleVariableDeclaration variableDeclaration = ast
                .newSingleVariableDeclaration();

        variableDeclaration.setType(ast.newPrimitiveType(PrimitiveType.INT));
        variableDeclaration.setName(ast.newSimpleName("id"));

        SingleVariableDeclaration variableDeclaration2 = ast
                .newSingleVariableDeclaration();

        variableDeclaration2.setType((Type) ASTNode
                .copySubtree(ast, loggerType));
        variableDeclaration2.setName(ast.newSimpleName("expr"));

        methodDeclaration.parameters().add(variableDeclaration);
        methodDeclaration.parameters().add(variableDeclaration2);

        org.eclipse.jdt.core.dom.Block block = ast.newBlock();
        ReturnStatement ret = ast.newReturnStatement();
        ret.setExpression(ast.newSimpleName("expr"));
        block.statements().add(ret);

        methodDeclaration.setBody(block);
        // System.out.println(methodDeclaration);
        return methodDeclaration;
    }

    private Type getType(AST ast, ITypeBinding bind) {// TODO !!!!!!!!!
        return ast.newSimpleType(ast.newName(bind.getQualifiedName()));
    }

    public final ICompilationUnit[] getTypes(IJavaProject javaproject) {
        ArrayList typeList = new ArrayList();
        try {
            IPackageFragmentRoot[] roots = javaproject
                    .getPackageFragmentRoots();
            // System.out.println("package roots "+roots);
            for (int i = 0; i < roots.length; i++) {
                IPackageFragmentRoot root = roots[i];
                if (root.getKind() == IPackageFragmentRoot.K_SOURCE) {
                    IJavaElement[] javaElements = root.getChildren();
                    for (int j = 0; j < javaElements.length; j++) {
                        IJavaElement javaElement = javaElements[j];
                        if (javaElement.getElementType() == IJavaElement.PACKAGE_FRAGMENT) {
                            IPackageFragment pf = (IPackageFragment) javaElement;
                            // System.out.println("pf "+pf);
                            ICompilationUnit[] compilationUnits = pf
                                    .getCompilationUnits();
                            typeList.addAll(Arrays.asList(compilationUnits));

                        }
                    }
                }
            }
        } catch (CoreException e) {
            e.printStackTrace();
        }
        ICompilationUnit[] types = new ICompilationUnit[typeList.size()];
        return (ICompilationUnit[]) typeList.toArray(types);
    }

    public void insertSeps(ICompilationUnit unit) {

        boolean junit = false;

        if (unit.getImport("junit.framework.*").exists()) {
            junit = true;
        }

        String source = "";

        try {
            source = unit.getBuffer().getContents();
        } catch (JavaModelException e) {
            // TODO Auto-generated catch block
            e.printStackTrace();
        }
        Document document = new Document(source);

        // creation of DOM/AST from a ICompilationUnit
        ASTParser parser = ASTParser.newParser(AST.JLS3);
        parser.setResolveBindings(true);

        parser.setSource(unit);

        CompilationUnit astRoot = (CompilationUnit) parser.createAST(null);

        InsertSepVisitor visitor = new InsertSepVisitor();
        astRoot.recordModifications();

        TypeDeclaration td = (TypeDeclaration) astRoot.types().get(0);

        ImportDeclaration importDeclaration = astRoot.getAST()
                .newImportDeclaration();

        importDeclaration.setName(astRoot.getAST().newSimpleName(
                VisualDebugger.debugPackage));
        importDeclaration.setOnDemand(true);
        astRoot.imports().add(importDeclaration);

        astRoot.accept(visitor);
        // creation of ASTRewrite
        types.addAll(visitor.getTypes());

        TextEdit edits = astRoot.rewrite(document, null);
        try {
            UndoEdit undo = edits.apply(document);
        } catch (MalformedTreeException e) {
            e.printStackTrace();
        } catch (BadLocationException e) {
            if (VisualDebugger.vdInDebugMode)
                e.printStackTrace();
        }

        // computation of the new source code
        try {
            edits.apply(document);
        } catch (MalformedTreeException e) {

            e.printStackTrace();
        } catch (BadLocationException e) {
            if (VisualDebugger.vdInDebugMode) {
                System.out.println(e.getLocalizedMessage());
                System.out.println(e.getMessage());
                e.printStackTrace();
            }
        }
        String newSource = document.get();

        String s = null;

        s = newSource;
        // s = astRoot.toString();
        String fn = unit.getPath().toString();
        String d = VisualDebugger.tempDir
                + fn.substring(1, fn.lastIndexOf(File.separator));
        File fil = new File(d);
        if (!fil.exists())
            fil.mkdirs();

        fn = fn.substring(fn.lastIndexOf(File.separator) + 1);

        File pcFile = new File(fil, fn);

        try {
            FileWriter fw = new FileWriter(pcFile);
            fw.write(s);
            fw.flush();
            fw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    public void insertSeps(IJavaProject project) {
        ICompilationUnit[] units = getTypes(project);
        types = new HashSet();
        debugCU = createDebuggerClass(AST.newAST(AST.JLS3));

        for (int i = 0; i < units.length; i++) {
            insertSeps(units[i]);
        }

        TypeDeclaration td = (TypeDeclaration) debugCU.types().get(0);

        for (Iterator it = types.iterator(); it.hasNext();) {
            ITypeBinding next = (ITypeBinding) it.next();
            td.bodyDeclarations().add(
                    getSepMethodDeclaration(debugCU.getAST(), this.getType(
                            debugCU.getAST(), next)));

        }

        td.bodyDeclarations().add(
                getSepMethodDeclaration(debugCU.getAST(), debugCU.getAST()
                        .newPrimitiveType(PrimitiveType.INT)));
        td.bodyDeclarations().add(
                getSepMethodDeclaration(debugCU.getAST(), debugCU.getAST()
                        .newPrimitiveType(PrimitiveType.BYTE)));
        td.bodyDeclarations().add(
                getSepMethodDeclaration(debugCU.getAST(), debugCU.getAST()
                        .newPrimitiveType(PrimitiveType.BOOLEAN)));
        td.bodyDeclarations().add(getSepMethodDeclaration(debugCU.getAST()));

               
        String projectPath = project.getPath().toOSString().substring(1);
        
        final String pathToDebugPackage = VisualDebugger.tempDir + projectPath + File.separator
                + VisualDebugger.debugPackage + File.separator;

        final String pathToDebugClass = pathToDebugPackage  + VisualDebugger.debugClass + ".java";

        new File(pathToDebugPackage).mkdirs();

        File pcFile = new File(pathToDebugClass);
        try {
            pcFile.createNewFile();
        } catch (IOException e1) {
            e1.printStackTrace();
        }

        try {
            final FileWriter fw = new FileWriter(pcFile);
            // FIXME: toString is only for debugging purpose, no warranty that it will
            // always generate a compilable output
            fw.write(debugCU.toString());
            fw.flush();
            fw.close();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    /**
     * @see IActionDelegate#rune(IAction)
     */
    public void run(IAction action) {

        
        if (selection == null) {
            return;
        }

        VisualDebugger.setDebuggingMode(true);

        final Main keyProver = Main.getInstance(false);

        // remove old environments
        while (VisualDebugger.getVisualDebugger().getMediator().getProof() != null) {
            keyProver.closeTaskWithoutIntercation();
        }


        VisualDebugger.getVisualDebugger();// .prepareKeY();

        if (selection != null && selection instanceof StructuredSelection) {
            IMethod selectedMethod = (IMethod) ((StructuredSelection) selection)
                    .getFirstElement();
            ICompilationUnit srcFile = selectedMethod.getCompilationUnit();

            if (srcFile == null) {
                MessageDialog.openError(PlatformUI.getWorkbench()
                        .getActiveWorkbenchWindow().getShell(),
                        "No Source Found.",
                        "The method you selected does not exist in source form. "
                                + "It cannot be used for a proof.");
                return;
            }

            File location = new File(VisualDebugger.tempDir);

            if (location.exists()) {
                delTemporaryDirectory();
            } else {
                location.mkdirs();
            }

            insertSeps(srcFile.getJavaProject());

            // TODO generalize to consider packageFragmentRoots (needed to
            // support
            // special source locations like folders only linked into the
            // eclipse
            // project
            IProject project = srcFile.getJavaProject().getProject();

            visualdebugger.Activator.getDefault().setProject(
                    srcFile.getJavaProject());

            visualdebugger.Activator.getDefault().setIProject(project);
            // assure the sources are parsed
            int status = assertProjectParsed(project, false);


            
            if (status == PROJECT_ALREADY_OPEN
                    || status == PROJECT_LOAD_SUCESSFUL) {
                // determine the encapsulating class of the selected method
                IType declaringType = selectedMethod.getDeclaringType();

                // extract signature of method
                // int paramCount = selectedMethod.getNumberOfParameters();
                try {
                    // selectedMethod.get
                    String[] parameterNames = selectedMethod
                            .getParameterNames();
                    String[] parameterTypes = selectedMethod
                            .getParameterTypes();
                    ListOfString sigStrings = SLListOfString.EMPTY_LIST;

                    for (int i = 0; i < parameterNames.length; i++) {
                        String javaType = EclipseSignaturesHelper
                                .determineJavaType(parameterTypes[i],
                                        declaringType);
                        if (javaType != null) {
                            sigStrings = sigStrings.append(javaType);
                        } else {
                            MessageDialog
                                    .openError(
                                            PlatformUI.getWorkbench()
                                                    .getActiveWorkbenchWindow()
                                                    .getShell(),
                                            "Error determining signature types !",
                                            "Could not resolve type "
                                                    + parameterTypes[i]
                                                    + " of the method's parameter "
                                                    + parameterNames[i]
                                                    + " !"
                                                    + " This is probably a syntax problem, check your import statements.");
                            return;
                        }
                    }

                    keyProver.toBack();
                    Main.setStandalone(false);

                    final JMLPOAndSpecProvider provider = keyProver
                            .getJMLPOAndSpecProvider();

                    ((JMLEclipseAdapter) provider).setMainVisible(false);

                    Vector methodSpecs = provider.getMethodSpecs(declaringType
                            .getFullyQualifiedName(), selectedMethod
                            .getElementName(), sigStrings);
                    final JMLMethodSpec spec = getMethodSpec(methodSpecs);
                    if (spec != null) {
                        startProver("Debugging "
                                + selectedMethod.getElementName(), provider,
                                spec, allInvariants, false, false);
                    } else {
                        dialog = new MethodPOSelectionDialog(PlatformUI
                                .getWorkbench().getActiveWorkbenchWindow()
                                .getShell(), methodSpecs);
                        state = dialog.open();

                        boolean allInvariants = dialog
                                .isAllInvariantsSelected();
                        boolean addInvariantsToPostCondition = dialog
                                .isAddInvariantsToPostConditionSelected();

                        if (state == Window.OK) {
                            Object selectedPO = dialog.getSelectionOnOK()
                                    .getFirstElement();

                            // TODO complete this step-by-step
                            // assignable: see JML Specification browser
                            // boolean assignablePO = (selectedPO instanceof
                            // AssignableCheckProofOblInput);
                            if (selectedPO instanceof AssignableCheckProofOblInput) {
                                AssignableCheckProofOblInput assignableCheckPO = (AssignableCheckProofOblInput) selectedPO;
                                startProver("Debugging "
                                        + selectedMethod.getElementName(),
                                        provider, assignableCheckPO.getSpec(),
                                        allInvariants,
                                        addInvariantsToPostCondition, true);
                            } else if (selectedPO instanceof JMLSpec) {
                                startProver("Debugging "
                                        + selectedMethod.getElementName(),
                                        provider, (JMLSpec) selectedPO,
                                        allInvariants,
                                        addInvariantsToPostCondition, false);
                            } else {
                                // TODO handle error case
                            }
                        }
                    }
                } catch (JavaModelException e) {
                    // TODO Auto-generated catch block
                    e.printStackTrace();
                }
            }
        }

        VisualDebugger.getVisualDebugger().initialize();
    }

    /**
     * @see IActionDelegate#selectionChanged(IAction, ISelection)
     */
    public void selectionChanged(IAction action, ISelection selection) {
        this.selection = selection;
    }

    /**
     * @see IObjectActionDelegate#setActivePart(IAction, IWorkbenchPart)
     */
    public void setActivePart(IAction action, IWorkbenchPart targetPart) {
        if (selection == null) {
            action.setEnabled(false);
        }
        action.setEnabled(true);
    }

    private void startProver(String debuggerEventMsg,
            final JMLPOAndSpecProvider provider, final JMLSpec spec,
            final boolean allInvariants, final boolean invPost,
            final boolean assignable) {
        VisualDebugger.getVisualDebugger().fireDebuggerEvent(
                new DebuggerEvent(DebuggerEvent.PROJECT_LOADED_SUCCESSFUL,
                        debuggerEventMsg));
        provider.createPOandStartProver(spec, allInvariants, invPost,
                assignable);
    }
}
