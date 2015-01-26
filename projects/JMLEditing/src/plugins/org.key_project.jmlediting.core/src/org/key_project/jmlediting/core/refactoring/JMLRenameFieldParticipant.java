package org.key_project.jmlediting.core.refactoring;

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
import org.eclipse.ltk.core.refactoring.RefactoringStatus;
import org.eclipse.ltk.core.refactoring.participants.CheckConditionsContext;
import org.eclipse.ltk.core.refactoring.participants.RenameParticipant;
import org.key_project.jmlediting.core.dom.IASTNode;
import org.key_project.jmlediting.core.parser.IJMLParser;
import org.key_project.jmlediting.core.parser.ParserException;
import org.key_project.jmlediting.core.profile.IJMLProfile;
import org.key_project.jmlediting.core.profile.JMLPreferencesHelper;
import org.key_project.jmlediting.core.utilities.CommentLocator;
import org.key_project.jmlediting.core.utilities.CommentRange;
import org.key_project.jmlediting.core.utilities.JMLJavaResolver;
import org.key_project.jmlediting.core.utilities.JavaElementIdentifier;
import org.key_project.jmlediting.core.utilities.Range;
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
      // Cast Safe because of the Check in InitializerMethod
      final IField elem = (IField) this.element;
      final org.eclipse.jdt.core.dom.CompilationUnit cu = SharedASTProvider
            .getAST(elem.getCompilationUnit(), SharedASTProvider.WAIT_YES, null);
      final TypeDeclarationFinder finder = new TypeDeclarationFinder();
      cu.accept(finder);
      final List<TypeDeclaration> decls = finder.getDecls();
      final TypeDeclaration topDecl = decls.get(0);
      final ITypeBinding type = topDecl.resolveBinding();
      final JMLJavaResolver resolver = new JMLJavaResolver(type, type);
      // Uniquely identify the Element that shall be refactored
      final JavaElementIdentifier refGoal = new JavaElementIdentifier(
            elem.getElementName(), resolver.getTypeForName(elem
                  .getElementName()), elem.getDeclaringType());
      final Range[] occurences = this.getJMLOccurences(refGoal);
      // final ReplaceEdit edit = new ReplaceEdit(offset,
      // refGoal.getName().length(), this
      // .getArguments().getNewName());
      return null;
   }

   /**
    * finds all occurences of the element that has to be refactored.
    *
    * @return a Range Array that contains all occurences of the Keyword. NULL if
    *         no occurences were found.
    */
   private Range[] getJMLOccurences(final JavaElementIdentifier identifier)
         throws CoreException {
      CommentLocator loc = null;
      final IJavaProject[] projects = JDTUtil.getAllJavaProjects();
      // In each Project
      for (final IJavaProject project : projects) {
         // In each Package
         for (final IPackageFragment pac : project.getPackageFragments()) {
            // In each Compilation Unit
            for (final ICompilationUnit unit : pac.getCompilationUnits()) {
               loc = new CommentLocator(unit.getSource());
               // In each JML Comment
               for (final CommentRange range : loc.findJMLCommentRanges()) {
                  final IJMLProfile activeProfile = JMLPreferencesHelper
                        .getProjectActiveJMLProfile(project.getProject());
                  final IJMLParser parser = activeProfile.createParser();
                  IASTNode parseResult;
                  try {
                     parseResult = parser.parse(unit.getSource(), range);

                  }
                  catch (final ParserException e) {
                     // Invalid JML Code, do syntax coloring with the recovered
                     // node
                     parseResult = e.getErrorNode();

                  }
                  if (parseResult == null) {
                     // No parser recovery, so no highlightinh
                     return null;
                  }

               }
            }
         }
      }
      return null;
   }
}