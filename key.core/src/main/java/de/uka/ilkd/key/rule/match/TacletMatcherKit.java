/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match;

import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher;

import org.key_project.prover.rules.TacletMatcher;


/**
 * Abstract factory for the creation of taclet matcher.
 *
 * Use method {@link #getKit()} to get the concrete factory and call
 * {@link #createTacletMatcher(Taclet)} to create a matcher for a {@link Taclet}
 *
 * The active factory is chosen at runtime by passing a value for the system property
 * <code>taclet.match</code> Currently supported values are: {@code vm}. The
 * legacy matching algorithm is the one used since the beginning of KeY. It will soon become
 * deprecated and replaced y {@code vm} as default.
 */
public abstract class TacletMatcherKit {

    /**
     * The concrete factory for the vm based taclet matcher.
     */
    private static final class VMTacletMatcherKit extends TacletMatcherKit {
        @Override
        public TacletMatcher createTacletMatcher(Taclet taclet) {
            return new VMTacletMatcher(taclet);
        }
    }

    /**
     * sets up the concrete factory to use depending on the provided system property or the given
     * default if no property is set
     */
    private static final String TACLET_MATCHER_SELECTION_VALUE =
        System.getProperty("taclet.match", "vm");
    private static final TacletMatcherKit ACTIVE_TACLET_MATCHER_KIT;
    static {
        if ("vm".equals(TACLET_MATCHER_SELECTION_VALUE)) {
            ACTIVE_TACLET_MATCHER_KIT = new VMTacletMatcherKit();
        } else {
            throw new RuntimeException("Unknown taclet matcher selected.");
        }
    }

    /**
     * returns the currently enabled factory
     *
     * @return the concrete factory to create taclet matchers
     */
    public static TacletMatcherKit getKit() {
        return ACTIVE_TACLET_MATCHER_KIT;
    }

    /**
     * the creator method returning the matcher for the specified taclet
     *
     * @param taclet the {@link Taclet} for which to create a matcher
     * @return the matcher for the given taclet
     */
    public abstract TacletMatcher createTacletMatcher(Taclet taclet);
}
