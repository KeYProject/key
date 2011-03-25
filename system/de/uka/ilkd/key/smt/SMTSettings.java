// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.smt;

import java.util.Collection;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.rule.Taclet;

public interface SMTSettings {

    /**
     * Returns the timeout that should be used for a single solver (in
     * milliseconds).
     */
    public long getTimeout();

    /**
     * Returns the generic command that should be used for starting a solver of
     * type <code>type</code>.<br>
     * Allowed place holders:<br>
     * %f Filename %p Problem formula.
     */
    public String getCommand(SolverType type);

    /**
     * The path of the folder, where the smt files are stored temporarily.
     */
    public String getSMTTemporaryFolder();

    /**
     * Returns the maximum number of processes that are allowed to run
     * concurrently.
     */
    public int getMaxConcurrentProcesses();

    /**
     *<code>true</code> If the transitive relations in the sort hierarchy
     * should be explicitly modeled by formulas.
     * */
    public boolean useExplicitTypeHierarchy();

    /**
     * <code>true</code> If a concrete <code>null</code> object should be used.
     */
    public boolean instantiateNullAssumption();

    /**
     * @return <code>true</code> if taclets should be used as assumptions.
     */
    public boolean makesUseOfTaclets();

    /**
     * @return the maximum number of different generic sorts that is allowed
     *         within the taclets that are used.
     */
    public int getMaxNumberOfGenerics();

    /**
     * The set of taclets that should be used. Only supported taclets are used
     * by the translation. In case that a taclet is not supported, it is
     * ignored.
     */
    public Collection<Taclet> getTaclets(Services services);
    
    /**
     * Returns <code>true</code> if the uniqueness property should be translated 
     * by using the built-in mechanism of the solver.
     * Has only some effect if the solver supports a built in feature for uniqueness.
     */
    public boolean useBuiltInUniqueness();

}
