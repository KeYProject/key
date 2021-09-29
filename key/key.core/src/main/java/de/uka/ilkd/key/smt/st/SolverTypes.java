package de.uka.ilkd.key.smt.st;

import java.util.ArrayList;
import java.util.Collection;
import java.util.ServiceLoader;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * @author Alexander Weigl
 * @version 1 (9/29/21)
 */
public class SolverTypes {
    private SolverTypes() {

    }

    /**
     * Class for the Z3 solver. It makes use of the SMT2-format.
     */
    public static final SolverType Z3_SOLVER = new Z3SolverType();
    /**
     * Z3 with new modular translator
     */
    public static final SolverType Z3_NEW_TL_SOLVER = new Z3NewTLSolverType();

    /**
     * Class for the Z3 solver. It makes use of the SMT2-format.
     */

    public static final SolverType Z3_CE_SOLVER = new Z3CounterExampleSolverType();

    /**
     * CVC4 is the successor to CVC3.
     *
     * @author bruns
     */
    public static final SolverType CVC4_SOLVER = new CVC4SolverType();

    /**
     * CVC4 with the new translation
     */
    public static final SolverType CVC4_NEW_TL_SOLVER = new CVC4NewTLSolverType();

    private static Collection<SolverType> SOLVERS = new ArrayList<>(8);

    public static Collection<SolverType> getSolverTypes() {
        if (SOLVERS.isEmpty()) {
            ServiceLoader<SolverType> loader = ServiceLoader.load(SolverType.class);
            SOLVERS = StreamSupport
                    .stream(loader.spliterator(), false)
                    .collect(Collectors.toList());
        }
        return SOLVERS;
    }
}
