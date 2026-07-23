/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.strategy;

import java.lang.reflect.Array;
import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.*;
import java.util.concurrent.ConcurrentHashMap;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.feature.AbstractNonDuplicateAppFeature;
import de.uka.ilkd.key.strategy.feature.NonDuplicateAppFeature;

import org.key_project.prover.rules.Taclet;
import org.key_project.prover.strategy.Strategy;
import org.key_project.prover.strategy.costbased.CostClassifiable;
import org.key_project.prover.strategy.costbased.CostLocality;
import org.key_project.prover.strategy.costbased.feature.*;

import org.jspecify.annotations.Nullable;

/**
 * Decide whether a taclet's strategy cost is a pure function of
 * the rule app and its find-position subterm (plus the always-recomputed age term and
 * {@code NonDuplicateApp}-family vetoes). For such "cost-local" taclets the base re-cost performed
 * by {@link TacletAppContainer#createFurtherApps} on every peek round can be replaced by arithmetic
 * (carry the stored cost forward, refresh only the age term), avoiding the dominant
 * {@code Strategy.computeCost} work.
 *
 * <h2>Classification (sound-by-construction, default-impure)</h2>
 * A taclet is eligible iff every {@link Feature} reachable in its per-taclet cost bindings resolves
 * to local. Per feature, in order:
 * <ol>
 * <li><b>veto</b> ({@link AbstractNonDuplicateAppFeature}): a 0/Top guard. Collected and re-checked
 * at reuse time (an app that became a duplicate must still be dropped); not descended into.</li>
 * <li><b>explicit override</b>: {@link VolatileCost} forces non-local (the author wins).</li>
 * <li><b>{@link StableCost}</b>: local -- for a leaf that is the whole story; for a composite it
 * means "transparent": the walk still recurses into its child features, so it stays local only if
 * they all are. There is NO automatic "any feature with children is transparent" guess; a composite
 * is trusted only because its author annotated it after checking that its own computation
 * (including any non-Feature inputs such as projections/term-generators) is find-local. The
 * transparent combinators are annotated once (Sum/Shannon/Scale/Let/ComprehendedSum/...).</li>
 * <li><b>{@link WeakStableCost}</b>: weakly local -- the cost also reads the whole find formula
 * (not just the find subterm), so the taclet stays eligible but its cost is carried forward only
 * while that find formula is unchanged. The reuse site enforces this: an independent sibling
 * rewrite that {@link FindTacletAppContainer#isStillApplicable} tolerates (find subterm intact,
 * formula not) still forces a recompute. Recurses into children like {@link StableCost}.</li>
 * <li><b>otherwise</b> (unannotated): non-local (the SAFE default). A new feature -- leaf or
 * composite -- is non-local until someone reviews it and adds {@link StableCost}; forgetting costs
 * only performance, never soundness.</li>
 * </ol>
 * A {@link StableCost} composite is local only if, in addition to its child features, every
 * {@link TermGenerator} it holds is at least as local. A generator that walks below the find
 * ({@code SubtermGenerator}) is find-local; one that walks up to the find's ancestors
 * ({@code SuperTermGenerator}) is {@link WeakStableCost}; one that reads the whole sequent
 * ({@code SequentFormulasGenerator}) is non-local. The walk follows every value that is itself
 * cost-classifiable, projections and buffers included, and never arbitrary objects: the live
 * feature tree holds mutable scratch state that must not be traversed.
 *
 * <p>
 * Optional verification (<code>-Dkey.strategy.costReuse.verify</code>): when reuse is applied also
 * recompute the cost and log a warning on any mismatch, a development aid to catch a feature that
 * is mis-classified local (it should then get {@link VolatileCost}).
 */
public final class CostReuse {

    public static final boolean VERIFY = Boolean.getBoolean("key.strategy.costReuse.verify");

    private static final org.slf4j.Logger LOGGER =
        org.slf4j.LoggerFactory.getLogger(CostReuse.class);

    private CostReuse() {}

    /** Per-class locality, cached (class annotations are stable for the JVM run). */
    private static final Map<Class<?>, CostLocality> localityCache = new ConcurrentHashMap<>();
    /** Cached "not eligible for reuse" marker (the map forbids null values). */
    private static final Eligibility INELIGIBLE = new Eligibility(new Feature[0], false);

    /**
     * How an eligible taclet may reuse its cost.
     *
     * @param vetoes the {@link AbstractNonDuplicateAppFeature} guards to re-check at reuse time
     * @param weakStable {@code true} if some feature reads the whole find formula
     *        ({@link WeakStableCost}); such a cost may be reused only while that find formula is
     *        unchanged. {@code false} for a purely subterm-local ({@link StableCost}) taclet, whose
     *        cost may always be carried forward.
     */
    public record Eligibility(Feature[] vetoes, boolean weakStable) {
    }

    /**
     * @param strategy the goal's strategy; classified against its cost dispatchers (only used to
     *        obtain those -- never dereferenced beyond {@link #dispatchers})
     * @param proof the proof being worked on; supplies the per-proof classification cache
     * @param taclet the taclet whose cost is a candidate for reuse
     * @return how the taclet may reuse its cost, or {@code null} if it is not eligible at all.
     */
    public static @Nullable Eligibility eligibility(Strategy<?> strategy, Proof proof,
            Taclet taclet) {
        // Without cost dispatchers we cannot establish locality -> treat as ineligible, and do not
        // cache that verdict, so a later call with a classifiable strategy can still classify it.
        final List<RuleSetDispatchFeature> disp = dispatchers(strategy);
        if (disp.isEmpty()) {
            return null;
        }
        // The verdict is cached in the PROOF's ServiceCaches, NOT a static map: a taclet's locality
        // depends on the cost dispatchers in force (which differ with the taclet options), while
        // Taclet#equals is only name + find term. A cache shared across proofs would let one option
        // set read another's verdict for a same-named but structurally different taclet -- exactly
        // the static-cache hazard ServiceCaches exists to avoid. Per proof, it is also freed with
        // the proof. (ELIGIBLE => at least the top-level NonDuplicateApp veto, so the empty-veto
        // INELIGIBLE acts as the "not eligible" sentinel, the map forbidding null values.)
        final Map<Taclet, Object> cache = proof.getServices().getCaches()
                .getCostReuseClassificationCache();
        final Object e = cache.computeIfAbsent(taclet, t -> {
            final Eligibility res = classify(disp, t);
            return res == null ? INELIGIBLE : res;
        });
        return e == INELIGIBLE ? null : (Eligibility) e;
    }

    private static @Nullable Eligibility classify(List<RuleSetDispatchFeature> dispatchers,
            Taclet taclet) {
        final Set<Feature> vetoes = Collections.newSetFromMap(new IdentityHashMap<>());
        vetoes.add(NonDuplicateAppFeature.INSTANCE); // top-level veto, applies to every taclet
        final boolean[] local = { true };
        final boolean[] weakStable = { false };
        final Set<CostClassifiable> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        for (RuleSetDispatchFeature d : dispatchers) {
            var rs = taclet.getRuleSets();
            while (!rs.isEmpty()) {
                final Feature f = d.get(rs.head());
                if (f != null) {
                    walk(f, vetoes, local, weakStable, seen);
                }
                rs = rs.tail();
            }
        }
        return local[0] ? new Eligibility(vetoes.toArray(new Feature[0]), weakStable[0]) : null;
    }

    /**
     * Classify a cost component: for a transparent (STABLE/WEAK_STABLE) composite, recurse into
     * every child component so it stays local only if they all are (see the class comment).
     */
    private static void walk(CostClassifiable f, Set<Feature> vetoes, boolean[] local,
            boolean[] weakStable, Set<CostClassifiable> seen) {
        if (!local[0] || !seen.add(f)) {
            return;
        }
        if (f instanceof AbstractNonDuplicateAppFeature) {
            // the no-duplicate-application guard: collected as a veto to re-check at reuse time;
            // it is not a locality, so it neither recurses nor forces non-local.
            vetoes.add((Feature) f);
            return;
        }
        switch (localityOf(f)) {
            case VOLATILE -> local[0] = false;
            // Transparent: recurse into every child component -- a Feature, TermGenerator or
            // ProjectionToTerm, all of which receive the goal -- and stay local only if they all
            // are. WEAK_STABLE additionally reads the whole find formula, so reuse is gated on
            // that formula being unchanged (see Eligibility). Children are discovered reflectively
            // (see forEachChild), so authors annotate locality and never enumerate children.
            case WEAK_STABLE -> {
                weakStable[0] = true;
                forEachChild(f, child -> walk(child, vetoes, local, weakStable, seen));
            }
            case STABLE -> forEachChild(f, child -> walk(child, vetoes, local, weakStable, seen));
        }
    }

    /** The (cached) reuse-locality of a cost component, taken from its class annotation. */
    private static CostLocality localityOf(CostClassifiable f) {
        return localityCache.computeIfAbsent(f.getClass(), c -> f.locality());
    }

    /**
     * Apply {@code action} to each {@link CostClassifiable} child (a Feature, TermGenerator or
     * ProjectionToTerm) held one structural step inside {@code f}.
     */
    private static void forEachChild(CostClassifiable f,
            java.util.function.Consumer<CostClassifiable> action) {
        for (Field fld : allFields(f.getClass())) {
            if (Modifier.isStatic(fld.getModifiers()) || fld.getType().isPrimitive()) {
                continue;
            }
            try {
                fld.setAccessible(true);
                follow(fld.get(f), action);
            } catch (Throwable ignored) {
            }
        }
    }

    private static void follow(@Nullable Object o,
            java.util.function.Consumer<CostClassifiable> action) {
        if (o == null) {
            return;
        }
        if (o instanceof CostClassifiable cc) {
            action.accept(cc);
            return;
        }
        Class<?> c = o.getClass();
        if (c.isArray()) {
            if (!c.getComponentType().isPrimitive()) {
                int n = Array.getLength(o);
                for (int i = 0; i < n; i++) {
                    follow(Array.get(o, i), action);
                }
            }
            return;
        }
        if (o instanceof Iterable<?> it) {
            for (Object e : it) {
                follow(e, action);
            }
        }
        // Everything else is not a cost component and is not traversed -- notably TermFeature (its
        // compute() has no goal, so it is stable by construction), plus Name, RuleAppCost, ...
    }

    /**
     * Verification aid (only when {@link #VERIFY}): warn if a reused cost differs from the freshly
     * recomputed one, i.e. some feature is mis-classified local and should be {@link VolatileCost}.
     */
    static void warnMismatch(Taclet taclet, Object reused, Object fresh) {
        LOGGER.warn("cost-reuse mismatch for taclet {}: a feature is mis-classified local; "
            + "annotate it @VolatileCost (reused={}, fresh={})", taclet.name(), reused, fresh);
    }

    /**
     * The cost dispatchers to classify against, taken from the strategy of the goal being costed.
     * Must NOT be cached across strategies: different goals/proofs use different strategy instances
     * (and some are not {@link ModularJavaDLStrategy} at all). A stale or empty cached value would
     * make the {@link #walk} traverse nothing and thus classify every taclet as (wrongly) local.
     * When the strategy exposes no cost dispatchers, the taclet is treated as ineligible (see
     * {@link #vetoesIfEligible}) -- never as trivially local.
     */
    private static List<RuleSetDispatchFeature> dispatchers(Strategy<?> strategy) {
        return strategy instanceof ModularJavaDLStrategy m ? m.costRuleSetDispatchers() : List.of();
    }

    private static List<Field> allFields(Class<?> c) {
        List<Field> fs = new ArrayList<>();
        for (Class<?> k = c; k != null && k != Object.class; k = k.getSuperclass()) {
            fs.addAll(Arrays.asList(k.getDeclaredFields()));
        }
        return fs;
    }
}
