/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.strategy.costbased;

import org.key_project.prover.strategy.costbased.feature.StableCost;
import org.key_project.prover.strategy.costbased.feature.VolatileCost;
import org.key_project.prover.strategy.costbased.feature.WeakStableCost;

/**
 * A strategy cost component that is evaluated against a {@code Goal} and whose result may therefore
 * depend on the changing proof state: a {@code Feature}, a {@code TermGenerator} or a
 * {@code ProjectionToTerm} (all of which receive the goal). These are exactly the building blocks
 * the cost-reuse classifier ({@code CostReuse}) has to inspect, so they share a common
 * reuse-{@link #locality()}.
 *
 * <p>
 * {@code TermFeature} is deliberately NOT a {@code CostClassifiable}: its {@code compute} method
 * receives only the term, the mutable state and the (stable) services -- no goal -- so it cannot
 * read volatile proof state and is stable by construction.
 */
public interface CostClassifiable {

    /**
     * The reuse-locality of this component, taken from its {@link StableCost} /
     * {@link WeakStableCost} / {@link VolatileCost} class annotation. Unannotated components are
     * {@link CostLocality#VOLATILE} -- the safe default, meaning their cost is always recomputed.
     * Overriding this method lets a component compute its locality dynamically, but the
     * annotation-driven default is what the vast majority use.
     */
    default CostLocality locality() {
        Class<?> c = getClass();
        // An anonymous class carries no annotation of its own and cannot be annotated; its
        // locality is that of the class it extends, so the lookup climbs to the first named
        // class. Named classes do not inherit: a subclass declares its own locality, because
        // its overrides may change what the cost depends on.
        while (c != null && c.isAnonymousClass() && !hasLocalityAnnotation(c)) {
            c = c.getSuperclass();
        }
        if (c == null) {
            return CostLocality.VOLATILE;
        }
        if (c.isAnnotationPresent(VolatileCost.class)) {
            return CostLocality.VOLATILE;
        }
        if (c.isAnnotationPresent(WeakStableCost.class)) {
            return CostLocality.WEAK_STABLE;
        }
        if (c.isAnnotationPresent(StableCost.class)) {
            return CostLocality.STABLE;
        }
        return CostLocality.VOLATILE;
    }

    private static boolean hasLocalityAnnotation(Class<?> c) {
        return c.isAnnotationPresent(VolatileCost.class)
                || c.isAnnotationPresent(WeakStableCost.class)
                || c.isAnnotationPresent(StableCost.class);
    }
}
