///* This file is part of KeY - https://key-project.org
// * KeY is licensed under the GNU General Public License Version 2
// * SPDX-License-Identifier: GPL-2.0-only */
//package de.uka.ilkd.key.scripts;
//
///**
// * An assertion which essentially performs a cut.
// *
// * The only difference is that this implementation tampers with the labels of the resulting goals to
// * allow them to be
// * better recognized in the script engine.
// *
// * (Unlike in other systems, in KeY the assertion does not remove the original goal formula since
// * that is not well-defined in sequent calculus.)
// */
//public class AssertCommand extends CutCommand {
//
//    @Override
//    public String getName() {
//        return "assert";
//    }
//
//    @Override
//    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
//        var args = state().getValueInjector().inject(new Parameters(), arguments);
//        var node = state().getFirstOpenAutomaticGoal().node();
//        execute(state(), args);
//        // node.proof().getGoal(node.child(0)).setBranchLabel("Validity");
//        // node.proof().getGoal(node.child(1)).setBranchLabel("Usage");
//    }
//}
