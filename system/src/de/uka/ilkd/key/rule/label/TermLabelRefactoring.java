package de.uka.ilkd.key.rule.label;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.label.TermLabel;
import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.Rule;

/**
 * <p>
 * A {@link TermLabelRefactoring} is used by
 * {@link TermLabelManager#refactorLabels(Services, PosInOccurrence, Term, Rule, Goal, Term)}
 * to refactor the labels of each visited {@link Term}.
 * </p>
 * <p>
 * For more information about {@link TermLabel}s and how they are maintained
 * during prove read the documentation of interface {@link TermLabel}.
 * </p>
 * @author Martin Hentschel
 * @see TermLabel
 * @see TermLabelManager
 */
public interface TermLabelRefactoring extends RuleSpecificTask {
   /**
    * Defines if a refactoring is required and if so in which {@link RefactoringScope}.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten.
    * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied.
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The optional taclet {@link Term}.
    * @return The required {@link RefactoringScope}.
    */
   public RefactoringScope defineRefactoringScope(Services services,
                                                  PosInOccurrence applicationPosInOccurrence,
                                                  Term applicationTerm,
                                                  Rule rule,
                                                  Goal goal,
                                                  Term tacletTerm);

   /**
    * This method is used to refactor the labels of the given {@link Term}.
    * @param services The {@link Services} used by the {@link Proof} on which a {@link Rule} is applied right now.
    * @param applicationPosInOccurrence The {@link PosInOccurrence} in the previous {@link Sequent} which defines the {@link Term} that is rewritten.
    * @param applicationTerm The {@link Term} defined by the {@link PosInOccurrence} in the previous {@link Sequent}.
    * @param rule The {@link Rule} which is applied.
    * @param goal The optional {@link Goal} on which the {@link Term} to create will be used.
    * @param tacletTerm The optional taclet {@link Term}.
    * @param term The {@link Term} which is now refactored.
    * @param labels The new labels the {@link Term} will have after the refactoring.
    */
   public void refactoreLabels(Services services,
                               PosInOccurrence applicationPosInOccurrence,
                               Term applicationTerm,
                               Rule rule,
                               Goal goal,
                               Term tacletTerm,
                               Term term,
                               List<TermLabel> labels);

   /**
    * Possible refactoring scopes.
    * @author Martin Hentschel
    */
   public static enum RefactoringScope {
      /**
       * No refactoring required.
       */
      NONE,

      /**
       * Refactor direct children of the application term.
       */
      APPLICATION_DIRECT_CHILDREN,

      /**
       * Refactor children and grandchildren of the application term.
       */
      APPLICATION_CHILDREN_AND_GRANDCHILDREN_SUBTREE,

      /**
       * Refactor the whole sequent.
       */
      SEQUENT;
   }
}