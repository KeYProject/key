/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.testgen;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.settings.DefaultSMTSettings;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.settings.ProofDependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSMTSettings;
import de.uka.ilkd.key.settings.ProofIndependentSettings;
import de.uka.ilkd.key.smt.*;
import de.uka.ilkd.key.smt.lang.SMTSort;
import de.uka.ilkd.key.smt.model.Model;
import de.uka.ilkd.key.smt.solvertypes.SolverType;
import de.uka.ilkd.key.smt.solvertypes.SolverTypes;
import de.uka.ilkd.key.testgen.settings.TestGenerationSettings;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class ModelGenerator implements SolverLauncherListener {
    private static final Logger LOGGER = LoggerFactory.getLogger(ModelGenerator.class);

    private final Services services;

    private final Goal goal;

    private int count;


    // models that have been found until now
    private final List<Model> models;
    // how many models we are looking for
    private final int target;


    public ModelGenerator(Goal s, int target, Services services) {
        this.goal = s;
        this.services = services;
        this.target = target;
        models = new LinkedList<>();
        this.count = 0;
    }


    /**
     * Try finding a model for the term with z3.
     */
    public void launch() {
        LOGGER.debug("Launch {}", count++);
        SolverLauncher launcher = prepareLauncher();
        SolverType solver = SolverTypes.Z3_CE_SOLVER;
        SMTProblem problem = new SMTProblem(goal);
        launcher.addListener(this);
        launcher.launch(problem, services, solver);
    }

    /**
     * Creates a SolverLauncher with the appropriate settings.
     *
     * @return
     */
    private SolverLauncher prepareLauncher() {
        final TestGenerationSettings settings = TestGenerationSettings.getInstance();
        final ProofIndependentSMTSettings piSettings =
            ProofIndependentSettings.DEFAULT_INSTANCE.getSMTSettings().clone();


        piSettings.setMaxConcurrentProcesses(settings.getNumberOfProcesses());
        final ProofDependentSMTSettings pdSettings =
            ProofDependentSMTSettings.getDefaultSettingsData();
        pdSettings.setInvariantForall(settings.invariantForAll());
        // invoke z3 for counterexamples
        final DefaultSMTSettings smtsettings =
            new DefaultSMTSettings(pdSettings, piSettings, new NewSMTTranslationSettings(), null);
        return new SolverLauncher(smtsettings);
    }

    @Override
    public void launcherStopped(SolverLauncher launcher, Collection<SMTSolver> finishedSolvers) {

        for (SMTSolver solver : finishedSolvers) {
            SMTSolverResult result = solver.getFinalResult();
            if (result.isValid().equals(SMTSolverResult.ThreeValuedTruth.FALSIFIABLE)
                    && models.size() < target) {
                Model model = solver.getSocket().getQuery().getModel();
                models.add(model);
                addModelToTerm(model);


                if (models.size() >= target) {
                    finish();
                } else {
                    launch();
                }

            } else {
                finish();
            }
        }

    }



    /**
     * Changes the term such that when evaluated again with z3 another model will be generated. If
     * we have a model (c1=v1 & c2 = v2 & ...) where c1, c2, ... are integer constants we change the
     * term t to the following form: t & !(c1=v1 & c2 = v2 & ...)
     *
     * @param m the model
     * @return true if the term has been changed
     */
    private boolean addModelToTerm(Model m) {
        TermBuilder tb = services.getTermBuilder();
        Namespace<IProgramVariable> variables = services.getNamespaces().programVariables();
        Term tmodel = tb.tt();
        for (String c : m.getConstants().keySet()) {

            SMTSort sort = m.getTypes().getTypeForConstant(c);

            if (sort != null && sort.getId().equals(SMTObjTranslator.BINT_SORT)) {
                String val = m.getConstants().get(c);
                int value = Integer.parseInt(val);
                ProgramVariable v = (ProgramVariable) variables.lookup(c);
                Term termConst = tb.var(v);
                Term termVal = tb.zTerm(value);
                Term termEquals = tb.equals(termConst, termVal);
                tmodel = tb.and(tmodel, termEquals);
            }
        }


        if (!tmodel.equals(tb.tt())) {
            Term notTerm = tb.not(tmodel);
            SequentFormula sf = new SequentFormula(notTerm);
            goal.addFormula(sf, true, true);
            return true;
        }
        return false;

    }

    private void finish() {
        LOGGER.info("Finished: found {}", models.size());
        for (Model m : models) {
            LOGGER.info("\t{}", m.toString());
        }
    }

    @Override
    public void launcherStarted(Collection<SMTProblem> problems, Collection<SolverType> solverTypes,
            SolverLauncher launcher) {
    }

    public Term sequentToTerm(Sequent s) {

        ImmutableList<Term> ante = ImmutableSLList.nil();

        final TermBuilder tb = services.getTermBuilder();
        ante = ante.append(tb.tt());
        for (SequentFormula f : s.antecedent()) {
            ante = ante.append(f.formula());
        }

        ImmutableList<Term> succ = ImmutableSLList.nil();
        succ = succ.append(tb.ff());
        for (SequentFormula f : s.succedent()) {
            succ = succ.append(f.formula());
        }

        return tb.imp(tb.and(ante), tb.or(succ));

    }

}
