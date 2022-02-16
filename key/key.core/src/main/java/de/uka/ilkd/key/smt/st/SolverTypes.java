package de.uka.ilkd.key.smt.st;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.ServiceLoader;
import java.util.stream.Collectors;
import java.util.stream.StreamSupport;

/**
 * Facade for the management of {@link SolverType}.
 * This class holds references to common and known solver type instances.
 * <p>
 * To add a new solver type, use the service loader with the {@link SolverType} interface.
 *
 * @author Alexander Weigl
 * @version 1 (9/29/21)
 */
public class SolverTypes {
    private static final Collection<SolverType> SOLVERS = new ArrayList<>(8);

    private SolverTypes() {

    }

    /**
     * Tries to find a solver type instance of the given clazz.
     *
     * @param clazz the class of the solver type
     * @param <T>   the solver type
     * @return an instance of {@code T} or null if no such solver type was loaded.
     */
    @Nullable
    public static <T extends SolverType> T get(Class<T> clazz) {
        for (SolverType solverType : getSolverTypes()) {
            if(solverType.getClass() == clazz)
                return clazz.cast(solverType);
        }
        return null;
    }


    /**
     * Loads the known solver types via {@link ServiceLoader}. Result is cached.
     */
    @Nonnull
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
     * temporary: Z3 floating points
     */
    public static final SolverType Z3_FP_SOLVER = get(Z3NewTLFPOnlySolverType.class);

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
