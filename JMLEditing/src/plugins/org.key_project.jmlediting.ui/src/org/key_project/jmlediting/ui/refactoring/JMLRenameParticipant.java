package org.key_project.jmlediting.ui.refactoring;

import java.util.LinkedList;

import org.eclipse.core.filebuffers.FileBuffers;
import org.eclipse.core.filebuffers.ITextFileBuffer;
import org.eclipse.core.filebuffers.ITextFileBufferManager;
import org.eclipse.core.filebuffers.LocationKind;
import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.ResourcesPlugin;
import org.eclipse.core.resources.mapping.IResourceChangeDescriptionFactory;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.NullProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.core.runtime.SubProgressMonitor;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IField;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.eclipse.ltk.core.refactoring.participants.ResourceChangeChecker;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.utilities.CommentRange;

/**
 * Class to participate in the rename refactoring of java fields by 
 * replacing the occurrences of that field in all the JML comments of the active file
 * 
 * Note: this class is not intended to be extended, instantiated or subclassed by clients
 * 
 * @author Robert Heimbach
 *
 * Testing: 
 *          No SWTBot Test implemented yet.
 *          Use /org.key_project.jmlediting.ui.test/data/template/RefactoringRenameTestClass.java
 *          and replace the field balance with a word of same length
 * 
 * Current Status: 
 *          Does not work when the new name, balance should change to, has a different length 
 *          because the java changes invalidate the positions of the JML text file changes.
 */
public class JMLRenameParticipant extends RenameParticipant {

    private TextFileChange fChange;
    private IField fField;
    private String fNewName;

    /**
     * {@inheritDoc}
     * 
     */
    @Override
    public String getName() {
        return "JML Refactoring Rename Participant";
    }

    /**
     * {@inheritDoc} Saves the new name and the field to be renamed.
     * 
     */
    @Override
    protected boolean initialize(Object element) {
        fNewName = getArguments().getNewName();

        // Saves the field to be renamed
        if (element instanceof IField) {
            fField = (IField) element;
            return true;
        }
        else {
            return false;
        }
    }

    /**
     * Only for testing purposes when resolving does not work yet. Provides
     * locations to change the variable "balance"
     * 
     * @param sameLength
     * @return
     */
    private LinkedList<CommentRange> initializePositionsToChange() {

        LinkedList<CommentRange> positionsInText = new LinkedList<CommentRange>();
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
     * {@inheritDoc}
     * 
     */
    @Override
    public RefactoringStatus checkConditions(IProgressMonitor pm,
            CheckConditionsContext context) throws OperationCanceledException {

        if (pm == null)
            pm = new NullProgressMonitor();

        pm.beginTask("", 100); //$NON-NLS-1$

        try {
            // Get the text file to be changed by going down the compilation
            // hierarchy. Getting the file's compilation unit, its
            // FileBufferManager, its Path and its FileBuffer first
            ICompilationUnit unit = fField.getCompilationUnit();
            if (unit == null)
                return RefactoringStatus
                        .createErrorStatus("Compilation Unit could not be found");

            ITextFileBufferManager manager = FileBuffers
                    .getTextFileBufferManager();
            if (manager == null)
                return RefactoringStatus
                        .createErrorStatus("TextFileBufferManager could not be found");

            IPath pathToSourceFile = unit.getPath();

            ITextFileBuffer buffer = manager.getTextFileBuffer(
                    pathToSourceFile, LocationKind.IFILE);
            if (buffer == null)
                return RefactoringStatus
                        .createErrorStatus("TextFileBuffer could not be found");

            // IDocument document = buffer.getDocument();

            IFile file = ResourcesPlugin.getWorkspace().getRoot()
                    .getFile(pathToSourceFile);

            pm.worked(50);

            try { // Connect the FileBufferManager and create the changes
                manager.connect(pathToSourceFile, LocationKind.IFILE,
                        new SubProgressMonitor(pm, 25));

                // Initialize the Change(s) to be done
                fChange = new TextFileChange("", file); //$NON-NLS-1$
                MultiTextEdit fileChangeRootEdit = new MultiTextEdit();
                fChange.setEdit(fileChangeRootEdit);

                // Get the all the positions which need to change
                // Resolving will be called here in later versions
                LinkedList<CommentRange> positionsInText;
                positionsInText = initializePositionsToChange();
                // positionsInText =
                // getTextPositionsFromResolving(file,fField,...)

                // Aggregating all the changes by adding each to the
                // MultiTextEdit
                for (CommentRange cm : positionsInText) {
                    ReplaceEdit edit = new ReplaceEdit(
                            cm.getContentBeginOffset(), cm.getContentLength(),
                            fNewName);
                    fileChangeRootEdit.addChild(edit);
                }

                // Give the changes created in this participant to the
                // ResourceChangeChecker
                // to validate all the changes together

                // String changeDescription = Messages.format("", new Object[] {
                // fField.getElementName(), fNewName });
                // fChange.addTextEditChangeGroup(new TextEditChangeGroup(
                // fChange,
                // new TextEditGroup(changeDescription, fileChangeRootEdit)));

                ResourceChangeChecker checker = (ResourceChangeChecker) context
                        .getChecker(ResourceChangeChecker.class);
                IResourceChangeDescriptionFactory deltaFactory = checker
                        .getDeltaFactory();
                deltaFactory.change(file);
            }
            finally {
                manager.disconnect(pathToSourceFile, LocationKind.IFILE,
                        new SubProgressMonitor(pm, 25));
            }
        }
        catch (CoreException e) {
            throw new OperationCanceledException(
                    "File Manager failed to connect to the file to be changed");
        }
        finally {
            pm.done();
        }

        return new RefactoringStatus();
    }

    /**
     * {@inheritDoc}
     * 
     */
    @Override
    public Change createChange(IProgressMonitor pm) throws CoreException,
            OperationCanceledException {

        // ICompilationUnit unit = fField.getCompilationUnit();
        // if (unit == null)
        // return null;
        // ITextFileBufferManager manager =
        // FileBuffers.getTextFileBufferManager();
        // if (manager == null)
        // return null;
        // IPath pathToSourceFile = unit.getPath();
        // ITextFileBuffer buffer = manager.getTextFileBuffer(pathToSourceFile,
        // LocationKind.IFILE);
        // if (buffer == null)
        // return null;
        // IDocument document = buffer.getDocument();
        // System.out.println(document.get());

        // Changes from Java not yet done!!

        return fChange;
    }
}
