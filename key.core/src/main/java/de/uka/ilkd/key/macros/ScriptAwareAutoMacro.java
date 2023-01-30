//// This file is part of KeY - Integrated Deductive Software Design
////
//// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//// Universitaet Koblenz-Landau, Germany
//// Chalmers University of Technology, Sweden
//// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//// Technical University Darmstadt, Germany
//// Chalmers University of Technology, Sweden
////
//// The KeY system is protected by the GNU General
//// Public License. See LICENSE.TXT for details.
////
//
// package de.uka.ilkd.key.macros;
//
// import de.uka.ilkd.key.java.ProofCommandStatement;
// import de.uka.ilkd.key.logic.Name;
// import de.uka.ilkd.key.logic.PosInOccurrence;
// import de.uka.ilkd.key.proof.Goal;
// import de.uka.ilkd.key.proof.Proof;
// import de.uka.ilkd.key.rule.ProofCommandStatementRule;
// import de.uka.ilkd.key.rule.RuleApp;
// import de.uka.ilkd.key.speclang.njml.JmlParser.ProofCmdContext;
// import de.uka.ilkd.key.strategy.RuleAppCost;
// import de.uka.ilkd.key.strategy.RuleAppCostCollector;
// import de.uka.ilkd.key.strategy.Strategy;
//
// import java.util.IdentityHashMap;
// import java.util.Map;
//
// public class ScriptAwareAutoMacro extends StrategyProofMacro {
//
// public ScriptAwareAutoMacro() { super(); }
//
// private Map<Goal, ProofCmdContext> detectedProofs = new IdentityHashMap<>();
//
// @Override
// public String getName() {
// return "Script-aware auto mode";
// }
//
// @Override
// public String getCategory() {
// return "Auto Pilot";
// }
//
// @Override
// public String getDescription() {
// return "<html>TODO</ol>";
// }
//
// public Map<Goal, ProofCmdContext> getDetectedProofs() {
// return detectedProofs;
// }
//
// @Override
// public String getScriptCommandName() {
// return "script-auto";
// }
//
// private static final Name NAME = new Name("Script-aware filter strategy");
//
// private class ScriptAwareStrategy implements Strategy {
//
// private final Strategy delegate;
//
// public ScriptAwareStrategy(Proof proof, PosInOccurrence posInOcc) {
// this.delegate = proof.getActiveStrategy();
// }
//
// @Override
// public Name name() {
// return NAME;
// }
//
// @Override
// public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
// if (detectedProofs.containsKey(goal)) {
// // we had found a command earlier.
// return false;
// }
// if (app.rule() instanceof ProofCommandStatementRule) {
// detectedProofs.put(goal, ProofCommandStatementRule.getCommand(pio));
// }
// return delegate.isApprovedApp(app, pio, goal);
// }
//
// @Override
// public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
// RuleAppCostCollector collector) {
// delegate.instantiateApp(app, pio, goal, collector);
// }
//
// @Override
// public boolean isStopAtFirstNonCloseableGoal() {
// return false;
// }
//
// @Override
// public RuleAppCost computeCost(RuleApp app, PosInOccurrence pos, Goal goal) {
// return delegate.computeCost(app, pos, goal);
// }
// }
//
// @Override
// protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
// return new ScriptAwareStrategy(proof, posInOcc);
// }
// }
