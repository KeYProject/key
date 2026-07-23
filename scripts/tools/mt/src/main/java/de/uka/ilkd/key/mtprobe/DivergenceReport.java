/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.mtprobe;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;

/** Compares two runs (single-core baseline vs. a multi-core run) and describes where they diverge. */
public final class DivergenceReport {

    private DivergenceReport() {
    }

    /** One place a comparison site disagreed between the two runs. */
    public record Divergence(String site, String key, String baselineValue, String otherValue) {
    }

    /**
     * @param baseline the single-core run
     * @param other a multi-core run
     * @return the comparison-site keys whose value differs between the two runs (empty if none)
     */
    public static List<Divergence> compare(ProbeRun baseline, ProbeRun other) {
        final List<Divergence> divergences = new ArrayList<>();
        final Map<String, String> a = baseline.observations();
        final Map<String, String> b = other.observations();
        final TreeSet<String> keys = new TreeSet<>();
        keys.addAll(a.keySet());
        keys.addAll(b.keySet());
        for (String slot : keys) {
            final String av = a.get(slot);
            final String bv = b.get(slot);
            if (av == null || bv == null || !av.equals(bv)) {
                final int bar = slot.indexOf('|');
                divergences.add(new Divergence(slot.substring(0, bar), slot.substring(bar + 1),
                    av == null ? "<absent>" : av, bv == null ? "<absent>" : bv));
            }
        }
        return divergences;
    }

    /**
     * Renders a run's own invariant violations plus its divergences from the baseline.
     *
     * @param baseline the single-core run (used only to compare against)
     * @param other the multi-core run being described
     * @return a human-readable, multi-line report
     */
    public static String render(ProbeRun baseline, ProbeRun other) {
        final StringBuilder sb = new StringBuilder(512);
        sb.append("run '").append(other.label()).append("':\n");

        final List<ProbeRun.Violation> viol = other.violations();
        sb.append("  invariant violations (bugs): ").append(viol.size()).append('\n');
        for (int i = 0; i < Math.min(viol.size(), 10); i++) {
            sb.append("    [").append(viol.get(i).site()).append("] ")
                    .append(viol.get(i).detail()).append('\n');
        }
        if (viol.size() > 10) {
            sb.append("    ... (").append(viol.size() - 10).append(" more)\n");
        }
        // warnings are latent risks (e.g. rule-cost ties), present in the single-core run too;
        // shown as a count so they are not mistaken for bugs
        if (!other.warnings().isEmpty()) {
            sb.append("  warnings (latent risks, also in single-core): ")
                    .append(other.warnings().size()).append('\n');
        }

        final List<Divergence> div = compare(baseline, other);
        sb.append("  differs from the single-core baseline at ").append(div.size())
                .append(" comparison key(s)").append(div.isEmpty() ? "" : ":").append('\n');
        for (int i = 0; i < Math.min(div.size(), 10); i++) {
            final Divergence d = div.get(i);
            sb.append("    [").append(d.site()).append("] ").append(d.key()).append('\n')
                    .append("        single-core: ").append(d.baselineValue()).append('\n')
                    .append("        this run   : ").append(d.otherValue()).append('\n');
        }
        if (div.size() > 10) {
            sb.append("    ... (").append(div.size() - 10).append(" more)\n");
        }
        return sb.toString();
    }
}
