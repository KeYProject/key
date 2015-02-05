package org.key_project.jmlediting.core.refactoring;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IProgressMonitor;
import org.eclipse.core.runtime.OperationCanceledException;
import org.eclipse.jdt.core.ICompilationUnit;
import org.eclipse.jdt.core.IField;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IPackageFragment;
import org.eclipse.jdt.core.dom.ITypeBinding;
import org.eclipse.jdt.core.dom.TypeDeclaration;
import org.eclipse.jdt.ui.SharedASTProvider;
import org.eclipse.ltk.core.refactoring.Change;
import org.eclipse.ltk.core.refactoring.CompositeChange;
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
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
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLJavaVisibleFieldsComputer;
import org.key_project.jmlediting.core.utilities.JavaRefactoringElementInformationContainer;
import org.key_project.jmlediting.core.utilities.TypeDeclarationFinder;
import org.key_project.util.jdt.JDTUtil;

/**
 * Provides extended Rename Refactoring for Local Variables JML Comments.
 *
 * @author David Giessing
 *
 */
public class JMLRenameFieldParticipant extends RenameParticipant {

   /**
    * The element that shall be refactored.
    */
   private Object element;

   /**
    * initializes the RenameParticipant with the given element.
    *
    * @return true if element implements IField else returns false to not
    *         further be part of the refactoring
    */
   @Override
   protected boolean initialize(final Object element) {

      for (final Class<?> c : element.getClass().getInterfaces()) {
         if (c.equals(IField.class)) {
            this.element = element;
            // TODO: Activate
            return true;
         }
      }
      return false;
   }

   @Override
   public String getName() {
      return "JMLRenameFieldParticipant";
   }

   @Override
   public RefactoringStatus checkConditions(final IProgressMonitor pm,
         final CheckConditionsContext context)
               throws OperationCanceledException {
      return new RefactoringStatus();
   }

   @Override
   public Change createChange(final IProgressMonitor pm) throws CoreException,
   OperationCanceledException {
      System.out.println("Creating Changes");
      // Cast Safe because of the Check in InitializerMethod
      final IField elem = (IField) this.element;
      final org.eclipse.jdt.core.dom.CompilationUnit cu = SharedASTProvider
            .getAST(elem.getCompilationUnit(), SharedASTProvider.WAIT_YES, null);
      final TypeDeclarationFinder finder = new TypeDeclarationFinder();
      cu.accept(finder);
      final List<TypeDeclaration> decls = finder.getDecls();
      final TypeDeclaration topDecl = decls.get(0);
      final ITypeBinding type = topDecl.resolveBinding();
      final JMLJavaVisibleFieldsComputer resolver = new JMLJavaVisibleFieldsComputer(
            type);
      // Uniquely identify the Element that shall be refactored
      final JavaRefactoringElementInformationContainer refGoal = new JavaRefactoringElementInformationContainer(
            elem.getElementName(), resolver.getTypeForName(type,
                  elem.getElementName()), elem.getDeclaringType(), this
                  .getArguments().getNewName());
      final Change occurences = this.getJMLOccurences(refGoal, pm);
      return occurences;
   }

   /**
    * finds all occurences of the element that has to be refactored.
    *
    * @return a Range Array that contains all occurences of the Keyword. NULL if
    *         no occurences were found.
    */
   private Change getJMLOccurences(
         final JavaRefactoringElementInformationContainer identifier,
         final IProgressMonitor pm) throws CoreException {
      System.out.println("Getting Occurences");
      final Collection<Change> changes = new ArrayList<Change>();
      final CompositeChange change = new CompositeChange("JML Renaming Changes");
      CommentLocator loc = null;
      final IJavaProject[] projects = JDTUtil.getAllJavaProjects();
      // In each Project
      for (final IJavaProject project : projects) {
         // In each Package
         for (final IPackageFragment pac : project.getPackageFragments()) {
            // In each Compilation Unit
            for (final ICompilationUnit unit : pac.getCompilationUnits()) {
               String src = null;
               if (this.getTextChange(unit) != null) {
                  src = this.getTextChange(unit).getPreviewContent(pm);
                  System.out.println(src);
               }
               else {
                  src = unit.getSource();
               }
               loc = new CommentLocator(src);

               for (final CommentRange range : loc.findJMLCommentRanges()) {
                  if (!src.substring(range.getBeginOffset(),
                        range.getEndOffset()).contains(identifier.getName())) {
                     continue; // no occurences in this compilation unit
                  }

                  final IJMLProfile activeProfile = JMLPreferencesHelper
                        .getProjectActiveJMLProfile(project.getProject());
                  final IJMLParser parser = activeProfile.createParser();
                  IASTNode parseResult;
                  try {
                     parseResult = parser.parse(src, range);
                     final List<IASTNode> keywords = Nodes.getAllNodesOfType(
                           parseResult, NodeTypes.KEYWORD_APPL);
                     for (final IASTNode keywordApplNode : keywords) {

                        final IKeywordNode keywordNode = (IKeywordNode) keywordApplNode
                              .getChildren().get(0);
                        final IKeyword keyword = keywordNode.getKeyword();

                        final IASTNode contentNode = keywordApplNode
                              .getChildren().get(1);

                        final IKeywordContentRefactorer refactorer = keyword
                              .createRefactorer();
                        if (refactorer != null) {
                           changes.add(refactorer.refactorFieldRename(
                                 identifier, contentNode, unit, src));
                        }
                     }
                  }
                  catch (final ParserException e) {
                     // Parse Error, Refactoring in this JML Comment can not be
                     // provided, so go on with the next one
                     continue;
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