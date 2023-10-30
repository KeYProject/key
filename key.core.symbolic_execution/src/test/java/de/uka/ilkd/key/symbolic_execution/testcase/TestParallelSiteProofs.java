/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.testcase;

import java.io.IOException;
import java.util.LinkedList;
import java.util.List;
import javax.xml.parsers.ParserConfigurationException;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;
import de.uka.ilkd.key.symbolic_execution.ExecutionNodePreorderIterator;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionMethodReturn;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionNode;
import de.uka.ilkd.key.symbolic_execution.model.IExecutionVariable;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionEnvironment;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.xml.sax.SAXException;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * This test class makes sure that parallel site proofs are working. It is only verified that no
 * exception is thrown and not that correct results are computed.
 *
 * @author Martin Hentschel
 */
public class TestParallelSiteProofs extends AbstractSymbolicExecutionTestCase {
    private static final int NUMBER_OF_THREADS = 21;

    /**
     * Tests parallel site proofs on a new instantiate proof after applying "resume" on it.
     */
    @Test
    @Disabled("Commented out for the moment as Hudson throws an OOM Exception")
    public void xxxtestNewProof()
            throws ProofInputException, IOException, ParserConfigurationException, SAXException,
            ProblemLoaderException, InterruptedException {
        // Define test settings
        String javaPathInkeyRepDirectory = "/set/magic42/test/Magic42.java";
        String containerTypeName = "Magic42";
        final String methodFullName = "compute";
        String oraclePathInBaseDirFile = "/set/magic42/oracle/Magic42.xml";
        // Create proof environment for symbolic execution
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env =
            createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory,
                containerTypeName, methodFullName, null, false, false, false, false, false, false,
                false, false, false, false);
        try {
            // Resume
            resume(env.getUi(), env.getBuilder(), oraclePathInBaseDirFile, testCaseDirectory);
            // Do test steps
            doParallelSiteProofTest(env);
        } finally {
            env.dispose();
        }
    }

    /**
     * Tests parallel site proofs on a proof reconstructed from a *.proof file.
     */
    @Test
    public void testProofFile() throws ProblemLoaderException, InterruptedException {
        // Define test settings
        String javaPathInkeyRepDirectory = "/set/magic42/test/Magic42.proof";
        // Create proof environment for symbolic execution
        SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env =
            createSymbolicExecutionEnvironment(testCaseDirectory, javaPathInkeyRepDirectory, false,
                false, false, false, false, false, false, false, false, false, false);
        try {
            // Do test steps
            doParallelSiteProofTest(env);
        } finally {
            env.dispose();
        }
    }

    /**
     * Executes the test steps to make sure that parallel tests are working without thrown
     * {@link Exception}s.
     *
     * @param env The {@link SymbolicExecutionEnvironment} to use.
     */
    protected void doParallelSiteProofTest(
            SymbolicExecutionEnvironment<DefaultUserInterfaceControl> env)
            throws InterruptedException {
        // Create threads
        List<SiteProofThread<?>> threads = new LinkedList<>();
        ExecutionNodePreorderIterator iter =
            new ExecutionNodePreorderIterator(env.getBuilder().getStartNode());
        while (iter.hasNext() && threads.size() < NUMBER_OF_THREADS) {
            IExecutionNode<?> next = iter.next();
            if (next != null) {
                threads.add(new ExecutionVariableSiteProofThread(next));
            }
            if (next instanceof IExecutionMethodReturn) {
                threads.add(new ExecutionReturnValueSiteProofThread((IExecutionMethodReturn) next));
            }
        }
        // Make sure that the correct number of threads are available
        assertEquals(NUMBER_OF_THREADS, threads.size());
        // Start threads
        for (SiteProofThread<?> thread : threads) {
            thread.start();
        }
        // Wait for threads
        waitForThreads(threads, 20 * 1000);
        // Check result
        for (SiteProofThread<?> thread : threads) {
            // Make sure that no exception is thrown.
            if (thread.getException() != null) {
                Assertions.fail(thread.getException());
            }
            // Make sure that something was computed in site proofs.
            Assertions.assertNotNull(thread.getResult());
        }
    }

    /**
     * Waits until the given {@link Thread}s have terminated.
     *
     * @param threads The {@link Thread}s to wait for.
     */
    public static void waitForThreads(List<SiteProofThread<?>> threads, long timeout)
            throws InterruptedException {
        long start = System.currentTimeMillis();
        if (threads != null) {
            for (SiteProofThread<?> thread : threads) {
                thread.join(timeout);
                if (System.currentTimeMillis() > start + timeout) {
                    Assertions.fail("Timeout during wait for parallel site proofs.");
                }
                /*
                 * while (thread.isAlive()) { if (System.currentTimeMillis() > start + timeout) {
                 * Assertions.fail("Timeout during wait for parallel site proofs."); } try {
                 * Thread.sleep(100); } catch (InterruptedException e) { // Nothing to do. } }
                 */
            }
        }
    }

    /**
     * Utility {@link Thread} to execute a parallel site proof.
     *
     * @author Martin Hentschel
     */
    private static abstract class SiteProofThread<T> extends Thread {
        /**
         * A possibly caught exception.
         */
        private Exception exception;

        /**
         * The result of the executed site proof.
         */
        private T result;

        /**
         * Returns the caught exception.
         *
         * @return The caught exception.
         */
        public Exception getException() {
            return exception;
        }

        /**
         * Sets the caught exception.
         *
         * @param exception The caught exception.
         */
        protected void setException(Exception exception) {
            this.exception = exception;
        }

        /**
         * Returns the result of the site proof.
         *
         * @return The site proof result.
         */
        public T getResult() {
            return result;
        }

        /**
         * Sets the result of the site proof.
         *
         * @param result The site proof result.
         */
        protected void setResult(T result) {
            this.result = result;
        }
    }

    /**
     * A {@link Thread} which computes the variables of a given {@link IExecutionNode} via site
     * proofs.
     *
     * @author Martin Hentschel
     */
    private static class ExecutionVariableSiteProofThread
            extends SiteProofThread<IExecutionVariable[]> {
        /**
         * The {@link IExecutionNode} to read variables from.
         */
        private final IExecutionNode<?> node;

        /**
         * Constructor.
         *
         * @param node The {@link IExecutionNode} to read variables from.
         */
        public ExecutionVariableSiteProofThread(IExecutionNode<?> node) {
            this.node = node;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public void run() {
            try {
                setResult(node.getVariables());
            } catch (Exception e) {
                setException(e);
            }
        }
    }

    /**
     * A {@link Thread} which computes the method return value of a given
     * {@link IExecutionMethodReturn} via a site proof.
     *
     * @author Martin Hentschel
     */
    private static class ExecutionReturnValueSiteProofThread extends SiteProofThread<String> {
        /**
         * The {@link IExecutionMethodReturn} to read method return value from.
         */
        private final IExecutionMethodReturn returnNode;

        /**
         * Constructor
         *
         * @param returnNode The {@link IExecutionMethodReturn} to read method return value from.
         */
        public ExecutionReturnValueSiteProofThread(IExecutionMethodReturn returnNode) {
            this.returnNode = returnNode;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public void run() {
            try {
                setResult(returnNode.getNameIncludingReturnValue());
            } catch (Exception e) {
                setException(e);
            }
        }
    }
}
