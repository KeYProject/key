/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match;

import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher;

import org.key_project.prover.rules.TacletMatcher;


/**
 * Abstract factory for taclet matchers: {@link #getKit()} returns the active factory, and
 * {@link #createTacletMatcher(Taclet)} creates the matcher deciding where a taclet (a proof rule)
 * applies. The factory is selected by the system property {@code taclet.match}; the only
 * supported value is {@code vm}, the match-plan based {@link VMTacletMatcher}.
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
