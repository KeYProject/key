/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.example;

import java.io.File;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.AbstractOperationPO;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.SymbolicExecutionTreeBuilder;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.po.ProgramMethodPO;
import de.uka.ilkd.key.symbolic_execution.profile.SymbolicExecutionJavaProfile;
import de.uka.ilkd.key.symbolic_execution.strategy.CompoundStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.ExecutedSymbolicExecutionTreeNodesStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.SymbolicExecutionBreakpointStopCondition;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.ExceptionBreakpoint;
import de.uka.ilkd.key.symbolic_execution.strategy.breakpoint.IBreakpoint;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;
import de.uka.ilkd.key.util.MiscTools;

import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.StringUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Example application which symbolically executes {@code example/Number#equals(Number)}
 *
 * @author Martin Hentschel
 */
public class Main {
    private static final Logger LOGGER = LoggerFactory.getLogger(Main.class);

    /**
     * The program entry point.
     *
     * @param args The start parameters.
     */
    public static void main(String[] args) {
        File location = new File("example"); // Path to the source code folder/file or to a *.proof
                                             // file
        List<File> classPaths = null; // Optionally: Additional specifications for API classes
        File bootClassPath = null; // Optionally: Different default specifications for Java API
        List<File> includes = null; // Optionally: Additional includes to consider
        try {
            // Ensure that Taclets are parsed
            if (!ProofSettings.isChoiceSettingInitialised()) {
                KeYEnvironment<?> env =
                    KeYEnvironment.load(location, classPaths, bootClassPath, includes);
                env.dispose();
            }
            // Set Taclet options
            ChoiceSettings choiceSettings = ProofSettings.DEFAULT_SETTINGS.getChoiceSettings();
            Map<String, String> oldSettings = choiceSettings.getDefaultChoices();
            Map<String, String> newSettings = new HashMap<>(oldSettings);
            newSettings.putAll(MiscTools.getDefaultTacletOptions());
            newSettings.put("methodExpansion", "methodExpansion:noRestriction");
            choiceSettings.setDefaultChoices(newSettings);
            // Load source code
            KeYEnvironment<DefaultUserInterfaceControl> env =
                KeYEnvironment.load(SymbolicExecutionJavaProfile.getDefaultInstance(), location,
                    classPaths, bootClassPath, includes, true); // env.getLoadedProof() returns
                                                                // performed proof if a *.proof file
                                                                // is loaded
            try {
                // Find method to symbolically execute
                KeYJavaType classType = env.getJavaInfo().getKeYJavaType("Number");
                IProgramMethod pm = env.getJavaInfo().getProgramMethod(classType, "equals",
                    ImmutableSLList.<Type>nil().append(classType), classType);
                // Instantiate proof for symbolic execution of the program method (Java semantics)
                AbstractOperationPO po = new ProgramMethodPO(env.getInitConfig(),
                    "Symbolic Execution of: " + pm, pm, null, // An optional precondition
                    true, // Needs to be true for symbolic execution!
                    true); // Needs to be true for symbolic execution!
                // po = new ProgramMethodSubsetPO(...); // PO for symbolic execution of some
                // statements within a method (Java semantics)
                // po = new FunctionalOperationContractPO(...) // PO for verification (JML
                // semantics)
                Proof proof = env.createProof(po);
                // Create symbolic execution tree builder
                SymbolicExecutionTreeBuilder builder =
                    new SymbolicExecutionTreeBuilder(proof, false, // Merge branch conditions
                        false, // Use Unicode?
                        true, // Use Pretty Printing?
                        true, // Variables are collected from updates instead of the visible type
                              // structure
                        true); // Simplify conditions
                builder.analyse();
                // Optionally, create an SymbolicExecutionEnvironment which provides access to all
                // relevant objects for symbolic execution
                SymbolicExecutionEnvironment<DefaultUserInterfaceControl> symbolicEnv =
                    new SymbolicExecutionEnvironment<>(env, builder);
                printSymbolicExecutionTree("Initial State", builder);
                // Configure strategy for full exploration
                SymbolicExecutionUtil.initializeStrategy(builder);
                SymbolicExecutionEnvironment.configureProofForSymbolicExecution(proof, 100, false,
                    false, false, false, false);
                // Optionally, add a more advanced stop conditions like breakpoints
                CompoundStopCondition stopCondition = new CompoundStopCondition();
                // Stop after 100 nodes have been explored on each branch.
                stopCondition.addChildren(new ExecutedSymbolicExecutionTreeNodesStopCondition(100));
                // stopCondition.addChildren(new StepOverSymbolicExecutionTreeNodesStopCondition());
                // // Perform only a step over
                // stopCondition.addChildren(new
                // StepReturnSymbolicExecutionTreeNodesStopCondition()); // Perform only a step
                // return
                IBreakpoint breakpoint = new ExceptionBreakpoint(proof,
                    "java.lang.NullPointerException", true, true, true, true, 1);
                // Stop at specified breakpoints
                stopCondition.addChildren(new SymbolicExecutionBreakpointStopCondition(breakpoint));
                proof.getSettings().getStrategySettings()
                        .setCustomApplyStrategyStopCondition(stopCondition);
                // Perform strategy which will stop at breakpoint
                symbolicEnv.getProofControl().startAndWaitForAutoMode(proof);
                builder.analyse();
                printSymbolicExecutionTree("Stopped at Breakpoint", builder);
                // Perform strategy again to complete symbolic execution tree
                symbolicEnv.getProofControl().startAndWaitForAutoMode(proof);
                builder.analyse();
                printSymbolicExecutionTree("Stopped at Breakpoint", builder);
            } finally {
                env.dispose(); // Ensure always that all instances of KeYEnvironment are disposed
            }
        } catch (Exception e) {
            LOGGER.debug("Exception at '{}':", location, e);
        }
    }

    /**
     * Prints the symbolic execution tree as flat list into the console.
     *
     * @param title The title.
     * @param builder The {@link SymbolicExecutionTreeBuilder} providing the root of the symbolic
     *        execution tree.
     */
    protected static void printSymbolicExecutionTree(String title,
            SymbolicExecutionTreeBuilder builder) {
        System.out.println(title);
        System.out.println(StringUtil.repeat("=", title.length()));
        ExecutionNodePreorderIterator iterator =
            new ExecutionNodePreorderIterator(builder.getStartNode());
        while (iterator.hasNext()) {
            IExecutionNode<?> next = iterator.next();
            System.out.println(next);
            // next.getVariables(); // Access the symbolic state.
            // next.getCallStack(); // Access the call stack.
            // next.getPathCondition(); // Access the path condition.
            // next.getFormatedPathCondition(); // Access the formated path condition.
            // next... // Additional methods provide access to additional information.
            // Check also the specific sub types of IExecutionNode like IExecutionTermination.
        }
        System.out.println();
    }
}
