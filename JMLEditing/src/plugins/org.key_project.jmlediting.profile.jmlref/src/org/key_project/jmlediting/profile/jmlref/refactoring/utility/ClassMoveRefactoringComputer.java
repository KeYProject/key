package org.key_project.jmlediting.profile.jmlref.refactoring.utility;

import java.util.ArrayList;
import java.util.List;

import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.text.edits.ReplaceEdit;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.dom.IStringNode;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;

/**
 * 
 * @author Robert Heimbach, Maksim Melnik
 *
 */
public class ClassMoveRefactoringComputer extends
        DefaultMoveRefactoringComputer {

    String fOldFullQualName;
    
    /**
     * 
     * @param fOldPackName
     * @param fNewPackName
     * @param fOldFullQualName
     */
    public ClassMoveRefactoringComputer(String fOldPackName, String fNewPackName, String fOldFullQualName) {
        super(fOldPackName, fNewPackName);
        this.fOldFullQualName = fOldFullQualName;
    }

    protected List<IStringNode> filterStringNodes(List<IASTNode> nodesList) {
        final ArrayList<IStringNode> filteredList = new ArrayList<IStringNode>();
        String nodeString="";

        for (final IASTNode node: nodesList){
            final IStringNode stringNode = (IStringNode) node;
            if(fOldFullQualName.contains(stringNode.getString()))nodeString=nodeString+stringNode.getString();
            else nodeString="";
            if (nodeString.equals(fOldFullQualName)) {
                filteredList.add(stringNode);
            }
        }
        return filteredList;
    }

    @Override
    public ArrayList<ReplaceEdit> computeNeededChangesToJML(
            ICompilationUnit unit, IJavaProject project) throws JavaModelException {

        final ArrayList<ReplaceEdit> changesToMake = new ArrayList<ReplaceEdit>();

        // Look through the JML comments and find the potential references which need to be renamed
        final String source = unit.getSource();
        // return no changes if source doesn't contain our package.filename
        if(!source.contains(fOldFullQualName))return changesToMake;
        
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

}
