/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.mtprobe;

import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;

/**
 * Everything one run of a proof recorded: the value each comparison site produced for each key,
 * and any invariant violations. Written concurrently by the multi-core prover's worker threads,
 * so both collections are thread-safe.
 */
public final class ProbeRun {

    /** A determinism check that tripped during this run. */
    public record Violation(String site, String detail) {
    }

    private final String label;

    /** {@code site + "|" + key} to the value observed there. */
    private final Map<String, String> observations = new ConcurrentHashMap<>();

    private final List<Violation> violations = new CopyOnWriteArrayList<>();

    /** Latent risks (e.g. rule-cost ties); counted apart from violations -- these are not bugs. */
    private final List<Violation> warnings = new CopyOnWriteArrayList<>();

    ProbeRun(String label) {
        this.label = label;
    }

    public String label() {
        return label;
    }

    public Map<String, String> observations() {
        return observations;
    }

    public List<Violation> violations() {
        return violations;
    }

    public List<Violation> warnings() {
        return warnings;
    }

    void warn(String site, String detail) {
        warnings.add(new Violation(site, detail));
    }

    void observe(String site, String key, String value) {
        final String slot = site + "|" + key;
        final String previous = observations.putIfAbsent(slot, value);
        // Same decision, two different values, in ONE run: already a divergence, no second run
        // needed to see it. (Under the multi-core prover this is how a site catches a race directly.)
        if (previous != null && !previous.equals(value)) {
            violations.add(new Violation(site,
                "same key seen with two values in one run: key=" + key + " first=" + previous
                    + " then=" + value));
        }
    }

    void invariantViolated(String site, String detail) {
        violations.add(new Violation(site, detail));
    }
}
