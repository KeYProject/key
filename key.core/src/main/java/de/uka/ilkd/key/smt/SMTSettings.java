/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt;

import java.util.Collection;

import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.NewSMTTranslationSettings;
import de.uka.ilkd.key.smt.solvertypes.SolverType;

public interface SMTSettings {

    /**
     * Returns the timeout that should be used for a single solver (in milliseconds).
     */
    long getTimeout();


    long getTimeout(SolverType type);

    /**
     * The path of the folder, where the smt files are stored temporarily.
     */
    String getSMTTemporaryFolder();

    /**
     * Returns the maximum number of processes that are allowed to run concurrently.
     */
    int getMaxConcurrentProcesses();

    /**
     * <code>true</code> If the transitive relations in the sort hierarchy should be explicitly
     * modeled by formulas.
     */
    boolean useExplicitTypeHierarchy();

    /**
     * <code>true</code> If a concrete <code>null</code> object should be used.
     */
    boolean instantiateNullAssumption();

    /**
     * @return <code>true</code> if taclets should be used as assumptions.
     */
    boolean makesUseOfTaclets();

    /**
     * @return the maximum number of different generic sorts that is allowed within the taclets that
     *         are used.
     */
    int getMaxNumberOfGenerics();

    /**
     * The set of taclets that should be used. Only supported taclets are used by the translation.
     * In case that a taclet is not supported, it is ignored.
     */
    Collection<Taclet> getTaclets();

    /**
     * Returns <code>true</code> if the uniqueness property should be translated by using the
     * built-in mechanism of the solver. Has only some effect if the solver supports a built in
     * feature for uniqueness.
     */
    boolean useBuiltInUniqueness();

    /**
     * Returns <code>true</code> if a uninterpreted function should be used if the normal normal
     * multiplication is not supported. In case that such a function should not be used an exception
     * is thrown when a not supported multiplication occurs.
     */
    boolean useUninterpretedMultiplicationIfNecessary();

    /**
     * Returns <code>true</code> if for too big respective too small integers (integers that are not
     * supported) a constant should be introduced.
     */
    boolean useAssumptionsForBigSmallIntegers();

    /**
     * @return Returns the logic used by solvers using SMT-LIB-Format
     */
    String getLogic();

    long getMaximumInteger();

    long getMinimumInteger();

    /**
     * Returns the bit size used for modelling integers when looking for bounded counter examples.
     *
     * @return a positive integer indicating the bit-size
     */
    long getIntBound();

    /**
     * Returns the bit size used for modelling heaps when looking for bounded counter examples.
     *
     * @return a positive integer indicating the bit-size
     */
    long getHeapBound();

    /**
     * Returns the bit size used for modelling sequences when looking for bounded counter examples.
     *
     * @return a positive integer indicating the bit-size
     */
    long getSeqBound();

    /**
     * Returns the bit size used for modelling objects when looking for bounded counter examples.
     *
     * @return a positive integer indicating the bit-size
     */
    long getObjectBound();

    /**
     * Returns the bit size used for modelling location sets when looking for bounded counter
     * examples.
     *
     * @return a positive integer indicating the bit-size
     */
    long getLocSetBound();

    /**
     * Returns true if and only if the version should be checked each time a solver is started.
     */
    boolean checkForSupport();

    boolean invarianForall();

    NewSMTTranslationSettings getNewSettings();
}
