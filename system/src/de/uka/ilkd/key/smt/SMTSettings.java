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


package de.uka.ilkd.key.smt;

import java.util.Collection;

import de.uka.ilkd.key.rule.Taclet;

public interface SMTSettings {

    /**
     * Returns the timeout that should be used for a single solver (in
     * milliseconds).
     */
    public long getTimeout();


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
    public Collection<Taclet> getTaclets();
    
    /**
     * Returns <code>true</code> if the uniqueness property should be translated 
     * by using the built-in mechanism of the solver.
     * Has only some effect if the solver supports a built in feature for uniqueness.
     */
    public boolean useBuiltInUniqueness();
    
    /**
     * Returns <code>true</code> if a uninterpreted function should be used if the
     * normal normal multiplication is not supported. In case that such a function 
     * should not be used an exception is thrown when a not supported multiplication
     * occurs.
     * */
    public boolean useUninterpretedMultiplicationIfNecessary();
    
    /**
     * Returns <code>true</code> if for too big respective too small integers (integers that
     * are not supported) a constant should be introduced.
     */
    public boolean useAssumptionsForBigSmallIntegers();
    
    /**
     * @return Returns the logic used by solvers using SMT-Lib-Format
     */
    public String getLogic();
   
    public long getMaximumInteger();
    
    public long getMinimumInteger();
    
    /**
     * Returns the bit size used for modelling integers when looking for
     * bounded counter examples.
     * @return a positive integer indicating the bit-size
     */
    public long getIntBound();
    
    /**
     * Returns the bit size used for modelling heaps when looking for
     * bounded counter examples.
     * @return a positive integer indicating the bit-size
     */
    public long getHeapBound();
    
    /**
     * Returns the bit size used for modelling sequences when looking for
     * bounded counter examples.
     * @return a positive integer indicating the bit-size
     */
    public long getSeqBound();
    
    /**
     * Returns the bit size used for modelling objects when looking for
     * bounded counter examples.
     * @return a positive integer indicating the bit-size
     */
    public long getObjectBound();
    
    /**
     * Returns the bit size used for modelling location sets when looking for
     * bounded counter examples.
     * @return a positive integer indicating the bit-size
     */
    public long getLocSetBound(); 
    
    /**
     * Returns true if and only if the version should be checked each time a solver is started.
     */
    public boolean checkForSupport();
  

}
