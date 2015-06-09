package org.key_project.jmlediting.core.refactoring;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBuffer;
import org.eclipse.core.filebuffers.ITextFileBufferManager;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IPackageFragmentRoot;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.ui.SharedASTProvider;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IKeywordNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.profile.syntax.IKeyword;
import org.key_project.jmlediting.core.profile.syntax.IKeywordContentRefactorer;
import org.key_project.jmlediting.core.utilities.ChangeShiftContainer;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLJavaVisibleFieldsComputer;
import org.key_project.jmlediting.core.utilities.JavaRefactoringElementInformationContainer;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;

/**
 * Class to participate in the rename refactoring of java fields by replacing
 * the occurrences of that field in all the JML comments of the active file.
 *
 * @noextend
 * @author Robert Heimbach
 *
 *         Testing: No SWTBot Test implemented yet. Use
 *         /org.key_project.jmlediting
 *         .core.test/data/template/RefactoringRenameTestClass.java and replace
 *         the field balance with a word of same length
 *
 *         Current Status: Does not work when the new name, balance should
 *         change to, has a different length because the java changes invalidate
 *         the positions of the JML text file changes.
 */
public final class JMLRenameParticipant extends RenameParticipant {

    private TextFileChange fChange;
    private IField fField;
    private String fNewName;
    private String fOldName;
    private ICompilationUnit fUnit;

    /**
     * Name of this class. {@inheritDoc}
     */
    @Override
    public final String getName() {
        return "JML Field Refactoring Rename Participant";
    }

    /**
     * {@inheritDoc} Saves the new name and the field to be renamed.
     *
     */
    @Override
    protected final boolean initialize(final Object element) {
        fNewName = getArguments().getNewName();

        // Saves the field to be renamed
        if (element instanceof IField) {
            fField = (IField) element;
            fOldName = fField.getElementName();
            return true;
        }
        else {
            return false;
        }

    }

    /**
     * Only for testing purposes when resolving does not work yet. Provides
     * locations to change the variable "balance".
     *
     * @return Locations which should be changed to the new field name.
     */
    private LinkedList<CommentRange> initializePositionsToChange() {

        final LinkedList<CommentRange> positionsInText = new LinkedList<CommentRange>();
        positionsInText.add(new CommentRange(199, 359, 243, 249,
                CommentRange.CommentType.MULTI_LINE));
        positionsInText.add(new CommentRange(199, 359, 295, 301,
                CommentRange.CommentType.MULTI_LINE));
        positionsInText.add(new CommentRange(199, 359, 311, 317,
                CommentRange.CommentType.MULTI_LINE));
        positionsInText.add(new CommentRange(199, 359, 350, 356,
                CommentRange.CommentType.MULTI_LINE));

        return positionsInText;
    }

    /**
     * Computes the changes to be done and validates them.
     *
     * {@inheritDoc}
     */
    @Override
    public final RefactoringStatus checkConditions(final IProgressMonitor pm,
            final CheckConditionsContext context)
            throws OperationCanceledException {

        pm.beginTask("", 100); //$NON-NLS-1$

        try {
            // Get the text file to be changed by going down the compilation
            // hierarchy. Getting the file's compilation unit, its
            // FileBufferManager, its Path and its FileBuffer first
            fUnit = fField.getCompilationUnit();
            if (fUnit == null) {
                return RefactoringStatus
                        .createErrorStatus("Compilation Unit could not be found");
            }

            final ITextFileBufferManager manager = FileBuffers
                    .getTextFileBufferManager();
            if (manager == null) {
                return RefactoringStatus
                        .createErrorStatus("TextFileBufferManager could not be found");
            }

            final IPath pathToSourceFile = fUnit.getPath();

            final ITextFileBuffer buffer = manager.getTextFileBuffer(
                    pathToSourceFile, LocationKind.IFILE);
            if (buffer == null) {
                return RefactoringStatus
                        .createErrorStatus("TextFileBuffer could not be found");
            }

            final IFile file = ResourcesPlugin.getWorkspace().getRoot()
                    .getFile(pathToSourceFile);

            pm.worked(50);

            try { // Connect the FileBufferManager and create the changes
                manager.connect(pathToSourceFile, LocationKind.IFILE,
                        new SubProgressMonitor(pm, 25));

                // // Initialize the Change(s) to be done
                //                fChange = new TextFileChange("", file); //$NON-NLS-1$
                // final MultiTextEdit fileChangeRootEdit = new MultiTextEdit();
                // fChange.setEdit(fileChangeRootEdit);
                //
                // // Get the all the positions which need to change
                // LinkedList<CommentRange> positionsInText;
                // positionsInText = initializePositionsToChange();
                //
                // for (final CommentRange cm : positionsInText) {
                // final ReplaceEdit edit = new ReplaceEdit(
                // cm.getContentBeginOffset(), cm.getContentLength(),
                // fNewName);
                // fileChangeRootEdit.addChild(edit);
                // }
                //
                // // Give the changes created in this participant to the
                // // ResourceChangeChecker for validating together
                // final ResourceChangeChecker checker = (ResourceChangeChecker)
                // context
                // .getChecker(ResourceChangeChecker.class);
                // final IResourceChangeDescriptionFactory deltaFactory =
                // checker
                // .getDeltaFactory();
                // deltaFactory.change(file);
            }
            finally {
                manager.disconnect(pathToSourceFile, LocationKind.IFILE,
                        new SubProgressMonitor(pm, 25));
            }
        }
        catch (final CoreException e) {
            throw new OperationCanceledException(
                    "File Manager failed to connect to the file to be changed");
        }
        finally {
            pm.done();
        }

        return new RefactoringStatus();
    }

    /**
     * Returns the text file changes to be done. {@inheritDoc}
     *
     */
    @Override
    public Change createChange(final IProgressMonitor pm) throws CoreException,
            OperationCanceledException {

        // Cast Safe because of the Check in InitializerMethod
        final org.eclipse.jdt.core.dom.CompilationUnit cu = SharedASTProvider
                .getAST(fUnit, SharedASTProvider.WAIT_YES, null);
        final TypeDeclarationFinder finder = new TypeDeclarationFinder();
        cu.accept(finder);
        final List<TypeDeclaration> decls = finder.getDecls();
        final TypeDeclaration topDecl = decls.get(0);
        final ITypeBinding type = topDecl.resolveBinding();
        final JMLJavaVisibleFieldsComputer resolver = new JMLJavaVisibleFieldsComputer(
                type);
        // Uniquely identify the Element that shall be refactored
        final JavaRefactoringElementInformationContainer refGoal = new JavaRefactoringElementInformationContainer(
                fOldName, resolver.getTypeForName(type, fOldName),
                fField.getDeclaringType(), fNewName);
        final Change occurences = getJMLOccurences(refGoal, pm);
        return occurences;
    }

    /**
     * finds all occurences of the element that has to be refactored.
     *
     * @return a Range Array that contains all occurences of the Keyword. NULL
     *         if no occurences were found.
     */
    private Change getJMLOccurences(
            final JavaRefactoringElementInformationContainer identifier,
            final IProgressMonitor pm) throws CoreException {
        System.out.println("Getting Occurences");
        final Collection<Change> changes = new ArrayList<Change>();
        final CompositeChange change = new CompositeChange(
                "JML Renaming Changes");
        CommentLocator loc = null;
        final IJavaProject javaProject = fUnit.getJavaProject();

        final IPackageFragmentRoot[] packageRoots = javaProject
                .getAllPackageFragmentRoots();

        for (final IPackageFragmentRoot root : packageRoots) {
            // In each Package
            for (final IJavaElement packageElement : root.getChildren()) {
                final IPackageFragment packageFrag;
                if (packageElement.getElementType() == IJavaElement.PACKAGE_FRAGMENT) {
                    packageFrag = (IPackageFragment) packageElement;
                }
                else {
                    continue;
                }
                // In each Compilation Unit
                for (final ICompilationUnit unit : packageFrag
                        .getCompilationUnits()) {
                    String src = null;
                    int shift = 0;
                    if (getTextChange(unit) != null) {
                        src = getTextChange(unit).getPreviewContent(pm);
                        System.out.println(src);
                    }
                    else {
                        src = unit.getSource();
                    }
                    loc = new CommentLocator(src);

                    for (final CommentRange range : loc.findJMLCommentRanges()) {
                        if (src.substring(range.getBeginOffset(),
                                range.getEndOffset()).contains(fOldName)) {

                            final IJMLProfile activeProfile = JMLPreferencesHelper
                                    .getProjectActiveJMLProfile(javaProject
                                            .getProject());
                            final IJMLParser parser = activeProfile
                                    .createParser();
                            IASTNode parseResult;
                            try {
                                parseResult = parser.parse(src, range);
                                final List<IASTNode> keywords = Nodes
                                        .getAllNodesOfType(parseResult,
                                                NodeTypes.KEYWORD_APPL);
                                for (final IASTNode keywordApplNode : keywords) {

                                    final IKeywordNode keywordNode = (IKeywordNode) keywordApplNode
                                            .getChildren().get(0);
                                    final IKeyword keyword = keywordNode
                                            .getKeyword();

                                    final IASTNode contentNode = keywordApplNode
                                            .getChildren().get(1);

                                    final IKeywordContentRefactorer refactorer = keyword
                                            .createRefactorer();
                                    if (refactorer != null) {
                                        final ChangeShiftContainer container = refactorer
                                                .refactorFieldRename(
                                                        identifier,
                                                        contentNode, unit, src,
                                                        shift);
                                        changes.add(container.getChange());
                                        shift = container.getShift();
                                    }
                                }
                            }
                            catch (final ParserException e) {
                                // Parse Error, Refactoring in this JML Comment
                                // can
                                // not be
                                // provided, so go on with the next one
                                continue;
                            }
                        }
                    }
                }
            }
        }
        for (final Change c : changes) {
            change.add(c);
        }
        return change;
    }
}
