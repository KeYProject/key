package de.uka.ilkd.key.smt.st;

import javax.annotation.Nonnull;
import java.util.*;
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
	private static final Collection<SolverType> SOLVERS = new ArrayList<>(1);
	private static final Collection<SolverType> LEGACY_SOLVERS = new ArrayList<>(1);

	private SolverTypes() {

	}

	/**
	 * Tries to find a solver type instance of the given clazz.
	 *
	 * @param clazz the class of the solver type
	 * @param <T>   the solver type
	 * @return an instance of {@code T} or null if no such solver type was loaded.
	 */
	@SuppressWarnings("unchecked")
	// TODO This won't work if ModifiableSolverType is used :/
/*	@Nullable
	public static <T extends SolverType> T get(Class<T> clazz) {
		return (T) getSolverTypes().stream().filter(it -> it.getClass().equals(clazz))
				.findFirst().orElse(null);
	} */


	/**
	 * Loads the known {@link SolverLoader} solver loaders via {@link ServiceLoader}.
	 * These loaders are then used to load the known {@link SolverType} solver types.
     * Result is cached.
     */
	@Nonnull
	public static Collection<SolverType> getSolverTypes() {
		if (SOLVERS.isEmpty()) {
			ServiceLoader<SolverLoader> loaderLoader = ServiceLoader.load(SolverLoader.class);
			var s =
					StreamSupport.stream(loaderLoader.spliterator(), false)
							.collect(Collectors.toList());
			for (SolverLoader solverLoader : s) {
				SOLVERS.addAll(solverLoader.getSolvers());
				LEGACY_SOLVERS.addAll(solverLoader.getLegacySolvers());
			}
		}
		return new ArrayList<>(SOLVERS);
	}

	@Nonnull
	public static Collection<SolverType> getLegacySolvers() {
		if (SOLVERS.isEmpty()) {
			getSolverTypes();
		}
		return new ArrayList<>(LEGACY_SOLVERS);
	}

	public static final SolverType Z3_CE_SOLVER = getSolverTypes().stream().filter(it -> it.getClass()
					.equals(SolverTypeImpl.class) && ((SolverTypeImpl) it).getName()
					.equals("Z3_CE"))
			.findFirst().orElse(null);

	public static final SolverType Z3_SOLVER = getSolverTypes().stream().filter(it -> it.getClass()
					.equals(SolverTypeImpl.class) && ((SolverTypeImpl) it).getName()
					.equals("Z3 (Legacy Translation)"))
			.findFirst().orElse(null);

	public static final SolverType CVC4_SOLVER = getSolverTypes().stream().filter(it -> it.getClass()
					.equals(SolverTypeImpl.class) && ((SolverTypeImpl) it).getName()
					.equals("CVC4 (Legacy Translation)"))
			.findFirst().orElse(null);


	public interface SolverLoader {
		Collection<SolverType> getSolvers();
		Collection<SolverType> getLegacySolvers();
	}

}
