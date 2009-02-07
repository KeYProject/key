package de.uka.ilkd.key.smt;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

public interface SmtSolver {

    public static enum RESULTTYPE {VALID, INVALID, UNKNOWN}
    
    /**
     * This rule's name.
     */
    public String displayName();
    
    /**
     * This rule's name as Name object.
     */
    public abstract Name name();
    
    /**
     * Check, if the formula in the goal is valid.
     * @param goal The goal to be proven.
     * @param timeout The maximum time, that should be used to execute the external solver.
     *      Given in seconds. If the time is exceeded, UNKNOWN is returned.
     * @param services The service object wrapping different settings and variables.
     * @return VALID, INVALID or UNKNOWN.
     */
    public SmtSolver.RESULTTYPE isValid(Goal goal, int timeout, Services services);
    

    /**
     * Check, if the term is valid.
     * @param t The term to be proven.
     * @param timeout The maximum time, that should be used to execute the external solver.
     *      Given in seconds. If the time is exceeded, UNKNOWN is returned.
     * @param services The service object wrapping different settings and variables.
     * @return VALID, INVALID or UNKNOWN.
     */
    public SmtSolver.RESULTTYPE isValid(Term t, int timeout, Services services);

}
