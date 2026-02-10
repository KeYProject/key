package org.key_project.key.cli;

import de.uka.ilkd.key.control.UserInterfaceControl;
import de.uka.ilkd.key.macros.AutoMacro;
import de.uka.ilkd.key.macros.AutoPilotPrepareProofMacro;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.SequentialProofMacro;
import de.uka.ilkd.key.macros.SkipMacro;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import org.key_project.prover.engine.ProverTaskListener;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.util.collection.ImmutableList;

public class MeasuringMacro extends SequentialProofMacro {
    public Stats before = new Stats();
    public Stats after = new Stats();

    @Override
    public String getName() {
        return "MeasuringMacro";
    }

    @Override
    public String getCategory() {
        return "ci-only";
    }

    @Override
    public String getDescription() {
        return "like auto but with more swag";
    }

    @Override
    public ProofMacro[] createProofMacroArray() {
        return new ProofMacro[]{
                new AutoPilotPrepareProofMacro(),
                new GatherStatistics(before),
                new AutoMacro(),
                new GatherStatistics(after)
        };
    }

    public static class Stats {
        public int openGoals = 0;
        public int closedGoals = 0;
    }

    public static class GatherStatistics extends SkipMacro {
        private final Stats stats;

        public GatherStatistics(Stats stats) {
            this.stats = stats;
        }

        @Override
        public String getName() {
            return "gather-stats";
        }

        @Override
        public String getCategory() {
            return "ci-only";
        }

        @Override
        public String getDescription() {
            return "stat purpose";
        }

        @Override
        public boolean canApplyTo(Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc) {
            return true;
        }

        @Override
        public ProofMacroFinishedInfo applyTo(UserInterfaceControl uic, Proof proof, ImmutableList<Goal> goals, PosInOccurrence posInOcc, ProverTaskListener listener) throws InterruptedException {
            stats.openGoals = proof.openGoals().size();
            stats.closedGoals = proof.getClosedSubtreeGoals(proof.root()).size();
            return super.applyTo(uic, proof, goals, posInOcc, listener);
        }
    }
}