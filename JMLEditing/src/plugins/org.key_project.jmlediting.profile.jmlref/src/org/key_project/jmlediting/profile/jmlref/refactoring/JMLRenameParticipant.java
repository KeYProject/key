package org.key_project.jmlediting.profile.jmlref.refactoring;

import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.util.jdt.JDTUtil;

/**
 * Class to participate in the rename refactoring of java fields.
 * 
 * It uses the {@link CommentLocator} to get a list of all JML comments and 
 * the {@link Resolver} to determine if the field to be renamed is referenced.
 * The changes are added to the scheduled java changes as the JDT takes care of 
 * moving offsets in the editor and preview when several changes are made to the same file.
 * 
 * @author Robert Heimbach
 */
public class JMLRenameParticipant extends RenameParticipant {

    private IJavaElement fJavaElementToRename;
    private String fNewName;
    private String fOldName;

    /**
     * Name of this class. {@inheritDoc}
     */
    @Override
    public final String getName() {
        return "JML Field Refactoring Rename Participant";
    }

    /**
     * {@inheritDoc} Saves the new name to change to. Saves the old name and the
     * field to be changed as a IJavaElement to search for references to it.
     */
    @Override
    protected final boolean initialize(final Object element) {
        fNewName = getArguments().getNewName();

        if (element instanceof IJavaElement) {
            fJavaElementToRename = (IJavaElement) element;
            fOldName = fJavaElementToRename.getElementName();
            return true;
        }
        else {
            return false;
        }

    }

    /**
     * Do nothing.
     *
     * {@inheritDoc}
     */
    @Override
    public final RefactoringStatus checkConditions(final IProgressMonitor pm,
            final CheckConditionsContext context)
            throws OperationCanceledException {

        return new RefactoringStatus();
    }

    /**
     * Computes the changes which need to be done to the JML code and
     * add those to the changes to the java code which are already scheduled.
     * Returns null to indicate that only shared text changes are made.
     * 
     *  {@inheritDoc}
     *
     */
    @Override
    public Change createChange(final IProgressMonitor pm) throws CoreException,
            OperationCanceledException {

        IJavaProject[] projects;
        try {
            projects = JDTUtil.getAllJavaProjects();

            // In each Project
            for (final IJavaProject project : projects) {
                // In each Package
                for (final IPackageFragment pac : project.getPackageFragments()) {
                    // In each Compilation Unit
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {

                        final LinkedList<ReplaceEdit> changesToJML = computeNeededChangesToJML(
                                unit, project);

                        // Get scheduled changes to the java code
                        final TextChange changesToJavaCode = getTextChange(unit);

                        // add our edits to the java changes (computes the
                        // shifts of the words and the preview)
                        if (changesToJavaCode != null) {
                            for (final ReplaceEdit edit : changesToJML) {
                                changesToJavaCode.addEdit(edit);
                            }
                        }
                        else {
                            // TODO: changes to JML but not to Java
                        }
                    }
                }
            }
        }
        catch (final JavaModelException e) {
            return null;
        }
        return null;
    }

    /**
     * Computes the text changed which need to be done to JML code by finding
     * all JML comments in the file and asking the resolver if it references the
     * java element which is to be renamed.
     * 
     * @param unit
     *            ICompilation unit for which to create the changes
     * @param project
     *            project of the compilation unit
     * @return list of edits which need to be done
     * @throws JavaModelException
     *             thrown when the source file cannot be loaded from
     *             ICompilationUnit or he JMLcomments could not be received
     */
    private LinkedList<ReplaceEdit> computeNeededChangesToJML(
            final ICompilationUnit unit, final IJavaProject project)
            throws JavaModelException {
        final LinkedList<ReplaceEdit> changesToMake = new LinkedList<ReplaceEdit>();

        // Find the JML comments in the given source file
        final String source = unit.getSource();
        final CommentLocator loc = new CommentLocator(source);

        for (final CommentRange range : loc.findJMLCommentRanges()) {

            final List<IASTNode> nodesList = getJMLcomments(unit, project,
                    source, range);
            // NodeTypes.KEYWORD_APPL);

            // Step through the list of IASTNodes and ask the resolver if it
            // references the element to be renamed
            for (final IASTNode stringNode : nodesList) {
                //System.out.println("node = " + stringNode);

                if (isReferenceToRefactoredElement(unit, stringNode)) {
                    // Create the text change and add it to the list to be
                    // returned
                    final int startOffset = stringNode.getStartOffset();
                    final int length = stringNode.getEndOffset()
                            - stringNode.getStartOffset();

                    final ReplaceEdit edit = new ReplaceEdit(startOffset,
                            length, fNewName);

                    changesToMake.add(edit);
                    //System.out.println("Adding Replace Edit to Validate");
                }
            }
        }
        return changesToMake;
    }

    /**
     * Searches through a given CommentRange range in a ICompilationUnit from a
     * given IJavaProject and returns all JML comments as a potentially empty
     * List
     * 
     * @param unit
     *            ICompilationUnit to search through
     * @param project
     *            IJavaProject unit is in. Needed to get active JMLProfile for
     *            parser
     * @param source
     *            Source File to be used in the Parser
     * @param range
     *            CommentRange to be parsed
     * @return list of JML comments found
     * @throws JavaModelException
     *             could not access source of given ICompilationUnit
     */
    private List<IASTNode> getJMLcomments(final ICompilationUnit unit,
            final IJavaProject project, final String source, final CommentRange range)
            throws JavaModelException {

        List<IASTNode> nodesList = new LinkedList<IASTNode>();

        final IJMLProfile activeProfile = JMLPreferencesHelper
                .getProjectActiveJMLProfile(project.getProject());
        final IJMLParser parser = activeProfile.createParser();
        IASTNode parseResult;
        try {
            parseResult = parser.parse(source, range);
            nodesList = Nodes.getAllNodesOfType(parseResult, ExpressionNodeTypes.PRIMARY_EXPR);

//            System.out.println();
//            System.out.println("found keywords "
//                    + nodesList
//                    + " in "
//                    + source.substring(range.getBeginOffset(),
//                            range.getEndOffset() + 1));
        }
        catch (final ParserException e) {
            return new LinkedList<IASTNode>();
        }
        //System.out.println("Returning: " + nodesList);
        return nodesList;
    }

    /**
     * Checks if a given IASTNode in a given ICompilationUnit references the
     * element to be renamed
     * 
     * @param unit
     *            the ICompilationUnit the IASTNode is in
     * @param node
     *            IASTNode to check
     * @return true if the given IASTNode references the element to be renamed
     *         else false
     */
    private Boolean isReferenceToRefactoredElement(final ICompilationUnit unit,
            final IASTNode node) {
        
        // correct name?
        if (((node.getChildren().get(0).getType()) == ExpressionNodeTypes.IDENTIFIER) && 
        ((node.getChildren().get(0).getChildren().get(0).getType()) == NodeTypes.STRING)) {
            if (((IStringNode) node.getChildren().get(0).getChildren().get(0)).getString().equals(fOldName)) {
                
            final IResolver resolver = new Resolver();
            ResolveResult result = null;
            try {
                result = resolver.resolve(unit, node);
                while(resolver.hasNext()) {
                    result = resolver.next();
                }
            }
            catch (final ResolverException e) {
                LogUtil.getLogger().logError(e);
                return false;
            }

            if (result == null) {
                //System.out.println("Resolver returned null");
                return false;
            }
            else {

                //System.out.println("Resolve Type = " + result.getResolveType());

                final IJavaElement jElement = result.getBinding()
                        .getJavaElement();

                // Some Java Element found but is it the same?
                //System.out.println("Java Element == Element to be renamed is "
                //        + jElement.equals(fJavaElementToRename));

                return jElement.equals(fJavaElementToRename);
            }   
        }
            else // wrong name 
                return false;
        }
        else // not of correct type
            return false;
    }
}