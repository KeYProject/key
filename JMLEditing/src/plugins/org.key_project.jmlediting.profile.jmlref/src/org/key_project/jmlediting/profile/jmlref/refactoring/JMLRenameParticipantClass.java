package org.key_project.jmlediting.profile.jmlref.refactoring;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaElement;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.jdt.internal.core.JavaModel;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.TextChange;
import org.eclipse.ltk.core.refactoring.TextFileChange;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
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
import org.key_project.jmlediting.core.resolver.IResolver;
import org.key_project.jmlediting.core.resolver.ResolveResult;
import org.key_project.jmlediting.core.resolver.ResolveResultType;
import org.key_project.jmlediting.core.resolver.ResolverException;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.LogUtil;
import org.key_project.jmlediting.profile.jmlref.resolver.Resolver;
import org.key_project.jmlediting.profile.jmlref.spec_keyword.spec_expression.ExpressionNodeTypes;
import org.key_project.util.jdt.JDTUtil;

public class JMLRenameParticipantClass extends RenameParticipant {

    private IJavaElement fJavaElementToRename;
    private String fNewName;
    private String fOldName;
    private IJavaProject fProject;  // the project which has the fields to be renamed

    /**
     * Name of this class. {@inheritDoc}
     */
    @Override
    public final String getName() {
        return "JML Class Refactoring Rename Participant";
    }

    /**
     * {@inheritDoc} Saves the new name to change to. Saves the old name and the
     * field to be changed as a IJavaElement to search for references to it. Saves
     * the active Project, i.e. the project which contains the class which field changes.
     */
    @Override
    protected final boolean initialize(final Object element) {
        fNewName = getArguments().getNewName();
        System.out.println("activated");
        if (element instanceof IJavaElement) {
            fJavaElementToRename = (IJavaElement) element;
            fProject = fJavaElementToRename.getJavaProject();
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

    @Override
    public Change createChange(final IProgressMonitor pm) {
        System.out.println("computing a change");
        return null;
    }
    
    /**
     * Computes the changes which need to be done to the JML code and
     * add those to the changes to the java code which are already scheduled.
     * 
     * @return Returns null if only shared text changes are made. Otherwise
     * returns a TextChange Object which gathered all the changes to JML annotations 
     * in class which does not have any Java changes scheduled.
     * 
     *  {@inheritDoc}
     *
     */
    @Override
    public Change createPreChange(final IProgressMonitor pm) throws CoreException,
            OperationCanceledException {
        
        System.out.println("computing a pre change");

        // Only non empty change objects will be added
        ArrayList<TextFileChange> changesToFilesWithoutJavaChanges = new ArrayList<TextFileChange>();
        
        // Find out the projects which need to be checked: active project plus all dependencies
        ArrayList<IJavaProject> projectsToCheck = new ArrayList<IJavaProject>();
        projectsToCheck.add(fProject);
        
        try {
            // Iterate through all java projects and check for projects which require the active project
            IJavaProject[] allProjects = JDTUtil.getAllJavaProjects();
            
            for (IJavaProject project: allProjects){
                String[] requiredProjectNames = project.getRequiredProjectNames();
                
                //System.out.println(project.getPath());
                //System.out.println(requiredProjectNames.length);
                
                if (requiredProjectNames.length > 0) {
                    
                    // To create an IJavaProject from the project's name
                    //IWorkspaceRoot workspaceRoot = ResourcesPlugin.getWorkspace().getRoot();
                    
                    for (String requiredProject: requiredProjectNames){
                        //System.out.println("required: "+requiredProject);
                        //System.out.println("project's name: "+fProject.getElementName());
                        
                        if (requiredProject.equals(fProject.getElementName())) {
                            //projectsToCheck.add(JavaCore.create(workspaceRoot.getProject(project)));
                            projectsToCheck.add(project);
                        }
                    } 
                }
            }
            
            // Look through all source files in each package and project
            for (final IJavaProject project : projectsToCheck) {
                for (final IPackageFragment pac : project.getPackageFragments()) {
                    for (final ICompilationUnit unit : pac
                            .getCompilationUnits()) {
                         
                        final ArrayList<ReplaceEdit> changesToJML = computeNeededChangesToJML(
                                unit, project);

                        // Get scheduled changes to the java code from the rename processor
                        final TextChange changesToJavaCode = getTextChange(unit);
                        
                       
                        // add our edits to the java changes
                        // JDT will compute the shifts and the preview
                        if (changesToJavaCode != null) {
                            for (final ReplaceEdit edit : changesToJML) {
                                changesToJavaCode.addEdit(edit);
                            }
                        }
                        else {
                            System.out.println("no changes to Java code for "+unit);
                            // In case changes to the JML code needs to be done (but not to the java code)
                            if (!changesToJML.isEmpty()){
                                
                                // Gather all the edits to the text (JML annotations) in a MultiTextEdit
                                // and add those to a change object for the given file
                                TextFileChange tfChange = new TextFileChange("", (IFile) unit.getCorrespondingResource());                         
                                MultiTextEdit allEdits = new MultiTextEdit();
                                
                                for (final ReplaceEdit edit: changesToJML) {
                                   allEdits.addChild(edit);
                                }

                                tfChange.setEdit(allEdits);
                                changesToFilesWithoutJavaChanges.add(tfChange);
                            }
                        }
                    }
                }
            }
        }
        catch (final JavaModelException e) {
            return null;
        }
        
        // Return null if only shared changes, otherwise gather changes to JML for classes with no java changes.
        if (changesToFilesWithoutJavaChanges.isEmpty())
            return null;
        else {
            CompositeChange allChangesToFilesWithoutJavaChanges = new CompositeChange("Changes to JML");
            for (TextFileChange change : changesToFilesWithoutJavaChanges){
                allChangesToFilesWithoutJavaChanges.add(change);
            }
   
            //allChangesToFilesWithoutJavaChanges.perform(pm);
            return allChangesToFilesWithoutJavaChanges;
            //return null;
        }
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
     * @return ArrayList of edits which need to be done
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
        final CommentLocator loc = new CommentLocator(source);

        for (final CommentRange range : loc.findJMLCommentRanges()) {

            final List<IASTNode> potentialReferences = getPotentialReferencesInJMLcomments(project,
                    source, range);

            for (final IASTNode node : potentialReferences) {

                resolvePotentialReferences(unit, node, changesToMake);
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
    private List<IASTNode> getPotentialReferencesInJMLcomments(final IJavaProject project, final String source, final CommentRange range)
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
        
        final List<IASTNode> primaries = getPrimaryNodes(filtedStringNodes, parseResult, !(activeProfile.getIdentifier().equals("org.key_project.jmlediting.profile.key")));
        
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
        
        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;     
            if (stringNode.getString().equals(fOldName)) {     
                filteredList.add(stringNode);
            }
        }
        
        return filteredList;
    }

    private List<IASTNode>getPrimaryNodes(final List<IStringNode> stringNodes, final IASTNode parseResult, final boolean notKeYProfile){
        final List<IASTNode> primaries = new ArrayList<IASTNode>();
        
        for (final IStringNode stringNode: stringNodes) {       
          final IASTNode primary = getPrimaryNode(parseResult, stringNode, notKeYProfile);
          // nested expressions would add the same primary twice, e.g. if code looks like this:
          // TestClass test;
          // //@ ensures this.test.test
          if (!primaries.contains(primary))
              primaries.add(primary);  
        }
        return primaries;
    }
    
    private IASTNode getPrimaryNode(final IASTNode context, final IStringNode toTest, final boolean notKeYProfile) {
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
                // If the KeY Profile is not used, the primary node from the assignable node
                // cannot be found. Resolver will still resolve the string node though.
                if (notKeYProfile && existing == null){
                    //System.out.println("primary found: null");
                    return toTest;
                }     
                else
                    return existing;
            }        
        }, null);
    }

    /**
     * Checks if a given {@link IASTNode} in a given {@link ICompilationUnit} references the
     * element to be renamed. It then creates the needed {@Link ReplaceEdit} and 
     * adds it to changesToMake.
     * 
     * @param unit
     *            the ICompilationUnit the IASTNode is in
     * @param node
     *            IASTNode of type Primary to resolve
     * @param changesToMake
     *            to accumulate needed changes 
     */
    private void resolvePotentialReferences(final ICompilationUnit unit, final IASTNode node, final ArrayList<ReplaceEdit> changesToMake) {
        
        final IASTNode nodeToChange = node;
    
        final IResolver resolver = new Resolver();
        ResolveResult result = null;
        try {
            int i = 0;
            result = resolver.resolve(unit, node);
            
            if (isReferencedElement(result)){
                computeReplaceEdit(changesToMake, nodeToChange);
            }
            
            if (result == null)
                i = 1;
                      
            while(resolver.hasNext()) { 
                 result = resolver.next();
                 
                 if (isReferencedElement(result)) {
                     // Access inner node which resolver checked by .next() method
                    if (nodeToChange.getChildren().size() >= 1) {
                         
                        final IASTNode child = nodeToChange.getChildren().get(1);
                         
                        if (child.getChildren().size() >= i) {
                             final IASTNode innerNode = nodeToChange.getChildren().get(1).getChildren().get(i);
                             computeReplaceEdit(changesToMake, innerNode);
                         }
                    }    
                 }
                 // Go to the next expression in the list which need to be checked
                 if (result != null && result.getResolveType().equals(ResolveResultType.METHOD)){
                     // In case of a Method Call like in test().test, the whole method call takes two list entries. 
                     // Thus we need to skip one more to resolve the <<test>> reference.
                     // List[113-125]
                     //    (MemberAccess[113-118](String[113-114](.),String[114-118](test)),
                     //     MethodCall[118-120](None[118-120]()),
                     //     MemberAccess[120-125](String[120-121](.),String[121-125](test)))
                     i = i + 2;
                 }
                 else {
                     i = i + 1;
                 }
            }
        }
        catch (final ResolverException e) {
            LogUtil.getLogger().logError(e);
        }
    }
    
    private Boolean isReferencedElement(final ResolveResult result){
        if (result == null) {
            return false;
        }
        
        final IJavaElement jElement = result.getBinding().getJavaElement();
        return jElement.equals(fJavaElementToRename);
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
        
        if(node.getType() == ExpressionNodeTypes.PRIMARY_EXPR) {
            changeThisNode = node.getChildren().get(0).getChildren().get(0);
        }
        
        // Keep the . when it is a member access like this.field
        if (node.getType() == ExpressionNodeTypes.MEMBER_ACCESS){
            changeThisNode = node.getChildren().get(1);
        }
        
        final int startOffset = changeThisNode.getStartOffset();
        final int length = changeThisNode.getEndOffset()
                - changeThisNode.getStartOffset();

        final ReplaceEdit edit = new ReplaceEdit(startOffset,
                length, fNewName);

        changesToMake.add(edit);
    }
    
}
