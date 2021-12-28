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

    public static <T extends SolverType> T get(Class<T> clazz) {
        return (T) getSolverTypes().stream().filter(it -> it.getClass().equals(clazz))
                .findFirst().orElse(null);
    }

    private static final Collection<SolverType> SOLVERS = new ArrayList<>(8);

    public static Collection<SolverType> getSolverTypes() {
        if (SOLVERS.isEmpty()) {
            ServiceLoader<SolverType> loader = ServiceLoader.load(SolverType.class);
            var s =
                    StreamSupport.stream(loader.spliterator(), false)
                            .collect(Collectors.toList());
            SOLVERS.addAll(s);
        }
        return SOLVERS;
    }

    /**
     * Class for the Z3 solver. It makes use of the SMT2-format.
     */
    public static final SolverType Z3_SOLVER = get(Z3SolverType.class);


    /**
     * Z3 with new modular translator
     */
    public static final SolverType Z3_NEW_TL_SOLVER = get(Z3NewTLSolverType.class);

    /**
     * Class for the Z3 solver. It makes use of the SMT2-format.
     */

    public static final SolverType Z3_CE_SOLVER = get(Z3CounterExampleSolverType.class);

    /**
     * CVC4 is the successor to CVC3.
     *
     * @author bruns
     */
    public static final SolverType CVC4_SOLVER = get(CVC4SolverType.class);

    /**
     * CVC4 with the new translation
     */
    public static final SolverType CVC4_NEW_TL_SOLVER = get(CVC4NewTLSolverType.class);

}
