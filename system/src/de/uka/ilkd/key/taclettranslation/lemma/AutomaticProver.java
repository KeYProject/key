// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.taclettranslation.lemma;

import java.util.LinkedList;
import java.util.concurrent.TimeUnit;
import java.util.concurrent.locks.Condition;
import java.util.concurrent.locks.ReentrantLock;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.RuleApp;

/**
 * A very simple type of prover, but it is sufficient for the automatic lemmata
 * handling: Normally there is a mechanism for choosing the next goal in a
 * cyclic way if for the currently chosen goal no rules are left that could be
 * applied. This is not done within this automatic prover, because it is not
 * necessary: Either the proof can be closed or not.
 */
public class AutomaticProver {

        private ReentrantLock lock = new ReentrantLock();
        private Condition sleepCondition = lock.newCondition();
        private ReentrantLock awaitShutdown = new ReentrantLock();

        /**
         * Starts the prover with the following parameters.
         * @param proof
         * @param maxNumberOfRules
         * @param timeout
         * @throws InterruptedException
         *                 If the prover is interrupted by the user, this
         *                 exception is thrown
         */
        public void start(Proof proof, int maxNumberOfRules, long timeout)
                        throws InterruptedException {
                Worker worker = new Worker(proof, maxNumberOfRules);
                lock.lock();
                try {  // start the prover and wait until the prover has finished its job.
                        Thread thread = new Thread(worker,"Prover");
                        thread.start();
                        if (timeout < 0) {
                                sleepCondition.await();
                        } else {
                                sleepCondition.await(timeout,
                                                TimeUnit.MILLISECONDS);
                                thread.interrupt();
                        }
                } catch (InterruptedException e) {
                        // Interruption is okay
                } finally {
                        lock.unlock();
                        awaitShutdown.lock();
                        try {
                        	if (worker.getException() != null) {
                                if (worker.getException()
                                                instanceof InterruptedException) {
                                        throw (InterruptedException) worker
                                                        .getException();
                                }
                                throw new RuntimeException(
                                                worker.getException());
                        }
                       } finally {
                    	   awaitShutdown.unlock();
                       }
                }
        }


        /**
         * The core of the automatic prover runs in an own thread.
         */
        private class Worker implements Runnable {
                private Proof proof;
                private int maxNumberOfRules;
                private Throwable exception;

                public Worker(Proof proof, int maxNumberOfRules) {
                        super();
                        this.proof = proof;
                        this.maxNumberOfRules = maxNumberOfRules;
                }

                private LinkedList<Goal> copyGoals(ImmutableList<Goal> goals) {
                        LinkedList<Goal> result = new LinkedList<Goal>();
                        for (Goal goal : goals) {
                                result.add(goal);
                        }
                        return result;
                }

                public Throwable getException() {
                        return exception;
                }

                public void run() {
                    awaitShutdown.lock();
                    try {
                                LinkedList<Goal> openGoals = copyGoals(proof
                                                .openGoals());
                                int ruleCounter = 0;
                                while (!openGoals.isEmpty()
                                                && ruleCounter < maxNumberOfRules) {
                                        Goal goal = openGoals.getFirst();
                                        RuleApp app = getNextApp(goal);
                                        if (app == null) {
                                                openGoals.removeFirst();
                                        } else {
                                                ImmutableList<Goal> goals = goal
                                                                .apply(app);
                                                for (Goal res : goals) {
                                                        if (!res.equals(goal)) {
                                                                openGoals.add(res);
                                                        }
                                                }
                                                ruleCounter++;
                                                if (goal.node().isClosed()) {
                                                        openGoals.removeFirst();
                                                }
                                        }
                                }
                        } catch (Throwable e) {
                                exception = e;
                        } finally {
                                lock.lock();
                                try {
                                	sleepCondition.signalAll();
                                } finally {
                                	lock.unlock();
                                	awaitShutdown.unlock();
                                }
                        }
                }

                private RuleApp getNextApp(Goal goal) {
                        RuleApp app = goal.getRuleAppManager().next();
                        if (app == null) {
                                goal.ruleAppIndex().scanBuiltInRules(goal);
                                app = goal.getRuleAppManager().next();
                        }
                        return app;
                }

        }

}