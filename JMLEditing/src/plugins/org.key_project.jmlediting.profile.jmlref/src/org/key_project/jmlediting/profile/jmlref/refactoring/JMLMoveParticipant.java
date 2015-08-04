package org.key_project.jmlediting.profile.jmlref.refactoring;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IPath;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.MoveParticipant;
import org.eclipse.text.edits.MultiTextEdit;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.INodeTraverser;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.dom.NodeTypes;
import org.key_project.jmlediting.core.dom.Nodes;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.util.jdt.JDTUtil;

/**
 * Class to participate in the move refactoring of java fields.
 * 
 * It uses the {@link CommentLocator} to get a list of all JML comments.
 * The changes are added to the scheduled java changes as the JDT takes care of 
 * moving offsets in the editor and preview when several changes are made to the same file.
 * 
 * @author Maksim Melnik
 */
public class JMLMoveParticipant extends MoveParticipant {
    private IJavaElement fToMove;        // file
    private IPath destination;              // path of destination
    private IPath source;                   // path to file

    private String fDocName;                // file name
    
    private String fOldPackName;            // old package name
    private String fNewPackName;            // new package name

    /**
     * {@inheritDoc} Initializes the source and destination paths, aswell as the file to move itself.
     */
    @Override
    protected boolean initialize(Object element) {
        if(element instanceof IJavaElement){
            fToMove=(IJavaElement) element;                                                  // get file element
            source=fToMove.getPath();
            destination=((IJavaElement)getArguments().getDestination()).getPath();              // get destination path
            fDocName = fToMove.getElementName();
<<<<<<< HEAD
            fOldFullQualName=((IType) element).getFullyQualifiedName();
            
            // get the old and new package name , because we only want to replace package names, otherwise nested classes problem        
            fOldPackName = fOldFullQualName.substring(0, fOldFullQualName.indexOf(fDocName)-1);
            fNewPackName = ((PackageFragment) getArguments().getDestination()).getElementName();  
            
=======
            System.out.println(((IType) element).getFullyQualifiedName().substring(0)); 
            // assume out source foulder is named src and packages lie directly in source foulder
            fOldPackName=source.toString().substring(source.toString().indexOf("src/")+4, source.toString().lastIndexOf("/")).replaceAll("/", ".");
            fNewPackName=destination.toString().substring(source.toString().indexOf("src/")+4).replaceAll("/", ".");
                    
>>>>>>> 433fda398a40c050b82212f24b17a24c1ea35765
            return true;
        }else{
            return false;
        }
    }

    @Override
    public String getName() {
        return "JML Field Move Participant";
    }

    @Override
    public RefactoringStatus checkConditions(IProgressMonitor pm,
            CheckConditionsContext context) throws OperationCanceledException {
        return new RefactoringStatus();
    }

    @Override
    public Change createChange(IProgressMonitor pm) throws CoreException,
    OperationCanceledException {

        IJavaProject[] projects;
        try {
            projects = JDTUtil.getAllJavaProjects();

            // Look through all source files in each package and project
            for (final IJavaProject project : projects) {
                for (final IPackageFragment pac : project.getPackageFragments()) {
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {
                        // compute a change for each document 
                        final ArrayList<ReplaceEdit> changesToJML = computeNeededChangesToJML(
                                unit, project);

                        // Get scheduled changes to the java code from the rename processor
                        final TextChange changesToJavaCode = getTextChange(unit);

                        // add our edits to the java changes (computes the
                        // shifts of the words and the preview)
                        if (changesToJavaCode != null) {
                            for (final ReplaceEdit edit : changesToJML) {
                                changesToJavaCode.addEdit(edit);
                            }
                        }
                        else {
                            TextFileChange tfChange = new TextFileChange("", (IFile) unit.getCorrespondingResource());
                            MultiTextEdit allEdits = new MultiTextEdit();

                            for (final ReplaceEdit edit: changesToJML) {
                                allEdits.addChild(edit);
                            }

                            tfChange.setEdit(allEdits);

                            return tfChange;
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
     * Computes the text changes which need to be done to JML code by finding
     * all JML comments in the file and asking the resolver if it references the
     * java element which is to be renamed.
     * 
     * @param unit
     *            ICompilation unit for which to create the changes
     * @param project
     *            Project of the compilation unit
     * @return List of edits which need to be done
     * @throws JavaModelException
     *             Thrown when the source file cannot be loaded from
     *             ICompilationUnit or he JMLcomments could not be received
     */
    private ArrayList<ReplaceEdit> computeNeededChangesToJML(
            final ICompilationUnit unit, final IJavaProject project)
            throws JavaModelException {
        
        final ArrayList<ReplaceEdit> changesToMake = new ArrayList<ReplaceEdit>();

        // Look through the JML comments and find the potential references which need to be renamed
        final String source = unit.getSource();
        // return no changes if source doesn't contain our package.filename
        if(!source.contains(fOldPackName+"."+fDocName))return changesToMake;
        
        final CommentLocator loc = new CommentLocator(source);

        for (final CommentRange range : loc.findJMLCommentRanges()) {
            final List<IASTNode> foundReferences = getReferencesInJMLcomments(project,
                    source, range);

            for (final IASTNode node : foundReferences) {
                computeReplaceEdit(changesToMake, node);
            }
        }
        return changesToMake;
    }
    
    /**
     * Searches through a given CommentRange in a source file and returns 
     * all JML comments as a potentially empty List.
     * 
     * @param project
     *            IJavaProject the unit resides in. Needed to get active JMLProfile for
     *            parser
     * @param source
     *            String representation of the source file to be used in the {@link IJMLParser}
     * @param range
     *            CommentRange to be parsed
     * @return List of found JML comments
     * @throws JavaModelException
     *             Could not access source of given ICompilationUnit
     */
    private List<IASTNode> getReferencesInJMLcomments(final IJavaProject project, final String source, final CommentRange range)
            throws JavaModelException {

        List<IASTNode> stringNodes = new ArrayList<IASTNode>();
        
        final IJMLProfile activeProfile = JMLPreferencesHelper
                .getProjectActiveJMLProfile(project.getProject());
        final IJMLParser parser = activeProfile.createParser();
        IASTNode parseResult;
        try {
            parseResult = parser.parse(source, range);
            stringNodes = Nodes.getAllNodesOfType(parseResult, NodeTypes.STRING);
        }
        catch (final ParserException e) {
            return new ArrayList<IASTNode>();
        }
 
        //System.out.println("Unfiltered: "+stringNodes);
        final List<IStringNode> filtedStringNodes =  filterStringNodes(stringNodes);
        //System.out.println("Filtered: "+filtedStringNodes);
        
        final List<IASTNode> primaries = getPrimaryNodes(filtedStringNodes, parseResult);
        
        //System.out.println("Primaries: " + primaries);
        return primaries;
    }
    
    /**
     * Filters a list of {@link IASTNode} for those which potentially reference 
     * the element to be renamed by comparing the name.
     * @param nodesList list to filter. Should be a list of IStringNodes.
     * @return filtered list
     */
    private ArrayList<IStringNode> filterStringNodes(final List<IASTNode> nodesList) {
        
        final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
        String nodeString="";
        
        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;
            nodeString=nodeString+stringNode.getString();
            // if the node contains our old package and ends with the name of our class , then our element is 100% referenced
            if (stringNode.getString().equals(fDocName) && nodeString.contains(fOldPackName)) {
                filteredList.add(stringNode);
            }
        }
        
        return filteredList;
    }
    
    
    private List<IASTNode>getPrimaryNodes(final List<IStringNode> stringNodes, final IASTNode parseResult){
        final List<IASTNode> primaries = new ArrayList<IASTNode>();
        
        for (final IStringNode stringNode: stringNodes) {       
          final IASTNode primary = getPrimaryNode(parseResult, stringNode);
          primaries.add(primary);  
        }
        return primaries;
    }
    
    private IASTNode getPrimaryNode(final IASTNode context, final IStringNode toTest) {
        return context.traverse(new INodeTraverser<IASTNode>() {

            @Override
            public IASTNode traverse(final IASTNode node, IASTNode existing) {
                if(node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
                    if(node.containsOffset(toTest.getStartOffset())) {
                        if(existing == null) {
                            existing = node;
                        } else if(node.getEndOffset() - node.getStartOffset() < existing.getEndOffset() - existing.getStartOffset()) {
                            existing = node;
                            return node;
                        }
                    }
                }
                return existing;
            }        
        }, null);
    }
    
    /**
     * Creates the text change and adds it to changesToMake.
     * 
     * @param changesToMake
     * @param node
     */
    private void computeReplaceEdit(final ArrayList<ReplaceEdit> changesToMake,
            final IASTNode node) {

        IASTNode changeThisNode = node;
        // WIRD IMMER ALS PRIMARY GESEHEN
        changeThisNode = node.getChildren().get(0).getChildren().get(0);
        
        final int startOffset = changeThisNode.getStartOffset();
        final int length = fOldPackName.length();

        changesToMake.add(new ReplaceEdit(startOffset, length, fNewPackName));
    }
}
