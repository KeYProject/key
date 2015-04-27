package org.key_project.key4eclipse.common.ui.counterExample;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.jface.preference.IPreferenceNode;
import org.eclipse.jface.preference.PreferenceManager;
import org.eclipse.jface.preference.PreferenceNode;
import org.eclipse.jface.resource.ImageDescriptor;
import org.eclipse.swt.widgets.Display;
import org.eclipse.ui.internal.dialogs.FilteredPreferenceDialog;
import org.key_project.util.eclipse.WorkbenchUtil;

import de.uka.ilkd.key.gui.smt.SMTSettings;
import de.uka.ilkd.key.gui.smt.SolverListener;
import de.uka.ilkd.key.gui.smt.SolverListener.InternSMTProblem;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.smt.SMTProblem;
import de.uka.ilkd.key.smt.SMTSolver;
import de.uka.ilkd.key.smt.SolverLauncher;
import de.uka.ilkd.key.smt.SolverLauncherListener;
import de.uka.ilkd.key.smt.SolverType;
import de.uka.ilkd.key.smt.counterexample.AbstractCounterExampleGenerator;
import de.uka.ilkd.key.smt.counterexample.AbstractSideProofCounterExampleGenerator;

/**
 * Implementation of {@link AbstractCounterExampleGenerator} which shows the
 * results in a {@link FilteredPreferenceDialog}.
 * @author Martin Hentschel
 */
@SuppressWarnings("restriction")
public class EclipseCounterExampleGenerator extends AbstractSideProofCounterExampleGenerator {
   /**
    * The {@link InternSMTProblem} to solve.
    */
   private final List<InternSMTProblem> problems = new LinkedList<InternSMTProblem>();
   
   /**
    * All found information.
    */
   private final List<InformationMessage> information = new LinkedList<InformationMessage>();
   
   /**
    * {@inheritDoc}
    */
   @Override
   protected SolverLauncherListener createSolverListener(SMTSettings settings, Proof proof) {
      return new SolverLauncherListener() {
         @Override
         public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes, SolverLauncher launcher) {
            handleLauncherStarted(problems, solverTypes, launcher);
         }
         
         @Override
         public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {
            handleLauncherStopped(launcher, finishedSolvers);
         }
      };
   }

   /**
    * When the {@link SolverLauncher} is started.
    * @param smtproblems The {@link SMTProblem}s.
    * @param solverTypes The {@link SolverType}s.
    * @param launcher The started {@link SolverLauncher}.
    */
   protected void handleLauncherStarted(Collection<SMTProblem> smtproblems, 
                                        Collection<SolverType> solverTypes, 
                                        SolverLauncher launcher) {
      // Create InternSMTProblem
      int x = 0;
      int y=0;
      for (SMTProblem problem : smtproblems) {
         y = 0;
         for (SMTSolver solver : problem.getSolvers()) {
            problems.add(new InternSMTProblem(x, y, problem, solver));
            y++;
         }
         x++;
      }
      // Check for warnings
      for (SolverType type : solverTypes) {
         if (type.supportHasBeenChecked() && !type.isSupportedVersion()) {
            information.add(new InformationMessage(SolverListener.computeSolverTypeWarningTitle(type), SolverListener.computeSolverTypeWarningMessage(type), false));
         }
      }
   }

   /**
    * When the {@link SolverLauncher} has been stopped.
    * @param launcher The stopped {@link SolverLauncher}.
    * @param finishedSolvers The finished {@link SMTSolver}.
    */
   protected void handleLauncherStopped(final SolverLauncher launcher, 
                                        final Collection<SMTSolver> finishedSolvers) {
      Display.getDefault().asyncExec(new Runnable() {
         @Override
         public void run() {
            showResultDialog();
         }
      });
   }
   
   /**
    * Shows the result dialog.
    */
   protected void showResultDialog() {
      // Create and dialog and PreferenceManager
      PreferenceManager manager = new PreferenceManager();
      SMTPreferenceDialog dialog = new SMTPreferenceDialog(WorkbenchUtil.getActiveShell(), manager);
      dialog.setHelpAvailable(false);
      // Fill PreferenceManager
      for (InternSMTProblem problem : problems) {
         if (problem.createInformation()) {
            information.add(new InformationMessage(SolverListener.createExceptionTitle(problem), problem, true));
         }
         manager.addToRoot(new SMTProblemPreferenceNode(computeProblemId(problem), 
                                                        computeProblemName(problem), 
                                                        null, 
                                                        problem));
      }
      if (!information.isEmpty()) {
         manager.addToRoot(new SMTInformationPreferenceNode("information", "Information", null, dialog, information));
      }
      // Show dialog;
      dialog.open();
   }

   /**
    * Computes the name of the given {@link InternSMTProblem}.
    * @param problem The {@link InternSMTProblem} to compute its name.
    * @return The computed name.
    */
   public static String computeProblemName(InternSMTProblem problem) {
      return problem.getProblem().getName() + " (" + problem.getSolver().getType().getName() + ")";
   }
   
   /**
    * Computes the unique ID of the given {@link InternSMTProblem}.
    * @param problem The {@link InternSMTProblem} to compute ID for.
    * @return The computed ID.
    */
   public static String computeProblemId(InternSMTProblem problem) {
      return "problem" + problem.getProblemIndex() + ", " + problem.getSolverIndex();
   }
   
   /**
    * A {@link PreferenceNode} which shows a {@link SMTProblemPropertyPage}.
    * @author Martin Hentschel
    */
   protected static class SMTProblemPreferenceNode extends PreferenceNode {
      /**
       * The solved {@link InternSMTProblem}.
       */
      private final InternSMTProblem problem;

      /**
       * Constructor.
       * @param id The node id.
       * @param label The label used to display the node in the preference dialog's tree.
       * @param image The image displayed left of the label in the preference dialog's tree, or {@code null} if none.
       * @param problem The solved {@link InternSMTProblem}.
       */
      public SMTProblemPreferenceNode(String id, 
                                      String label, 
                                      ImageDescriptor image, 
                                      InternSMTProblem problem) {
         super(id, label, image, null);
         this.problem = problem;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void createPage() {
         SMTProblemPropertyPage page = new SMTProblemPropertyPage(problem);
         if (getLabelImage() != null) {
            page.setImageDescriptor(getImageDescriptor());
         }
         page.setTitle(getLabelText());
         setPage(page);
      }
   }
   
   /**
    * A {@link PreferenceNode} which shows a {@link SMTProblemPropertyPage}.
    * @author Martin Hentschel
    */
   protected static class SMTInformationPreferenceNode extends PreferenceNode {
      /**
       * The {@link SMTProblemPreferenceNode} in which this {@link IPreferenceNode} is used.
       */
      private final SMTPreferenceDialog dialog;
      
      /**
       * All found information.
       */
      private final List<InformationMessage> informations;

      /**
       * Constructor.
       * @param id The node id.
       * @param label The label used to display the node in the preference dialog's tree.
       * @param image The image displayed left of the label in the preference dialog's tree, or {@code null} if none.
       * @param dialog The {@link SMTProblemPreferenceNode} in which this {@link IPreferenceNode} is used.
       * @param informations All found information.
       */
      public SMTInformationPreferenceNode(String id, 
                                          String label, 
                                          ImageDescriptor image, 
                                          SMTPreferenceDialog dialog,
                                          List<InformationMessage> informations) {
         super(id, label, image, null);
         this.dialog = dialog;
         this.informations = informations;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void createPage() {
         SMTInformationPropertyPage page = new SMTInformationPropertyPage(dialog, informations);
         if (getLabelImage() != null) {
            page.setImageDescriptor(getImageDescriptor());
         }
         page.setTitle(getLabelText());
         setPage(page);
      }
   }
   
   /**
    * An information message.
    * @author Martin Hentschel
    */
   public static class InformationMessage {
      /**
       * The title.
       */
      private final String title;
      
      /**
       * Optional additional data.
       */
      private final Object data;
      
      /**
       * {@code true} error, {@code false} warning.
       */
      private final boolean error;

      /**
       * Constructor.
       * @param title The title.
       * @param data Optional additional data.
       * @param error {@code true} error, {@code false} warning.
       */
      public InformationMessage(String title, Object data, boolean error) {
         this.title = title;
         this.data = data;
         this.error = error;
      }

      /**
       * Returns the title.
       * @return The title.
       */
      public String getTitle() {
         return title;
      }

      /**
       * Returns the optional additional data.
       * @return The Optional additional data.
       */
      public Object getData() {
         return data;
      }

      /**
       * Returns the error state.
       * @return {@code true} error, {@code false} warning.
       */
      public boolean isError() {
         return error;
      }
   }
}
