package org.key_project.jmlediting.core.refactoring;

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
            final ICompilationUnit unit = fField.getCompilationUnit();
            if (unit == null) {
                return RefactoringStatus
                        .createErrorStatus("Compilation Unit could not be found");
            }

            final ITextFileBufferManager manager = FileBuffers
                    .getTextFileBufferManager();
            if (manager == null) {
                return RefactoringStatus
                        .createErrorStatus("TextFileBufferManager could not be found");
            }

            final IPath pathToSourceFile = unit.getPath();

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

                // Initialize the Change(s) to be done
                fChange = new TextFileChange("", file); //$NON-NLS-1$
                final MultiTextEdit fileChangeRootEdit = new MultiTextEdit();
                fChange.setEdit(fileChangeRootEdit);

                // Get the all the positions which need to change
                LinkedList<CommentRange> positionsInText;
                positionsInText = initializePositionsToChange();

                for (final CommentRange cm : positionsInText) {
                    final ReplaceEdit edit = new ReplaceEdit(
                            cm.getContentBeginOffset(), cm.getContentLength(),
                            fNewName);
                    fileChangeRootEdit.addChild(edit);
                }

                // Give the changes created in this participant to the
                // ResourceChangeChecker for validating together
                final ResourceChangeChecker checker = (ResourceChangeChecker) context
                        .getChecker(ResourceChangeChecker.class);
                final IResourceChangeDescriptionFactory deltaFactory = checker
                        .getDeltaFactory();
                deltaFactory.change(file);
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

        return fChange;
    }
}
