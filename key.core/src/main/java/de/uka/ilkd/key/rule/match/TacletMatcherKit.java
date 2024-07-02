package de.uka.ilkd.key.rule.match;

import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletMatcher;
import de.uka.ilkd.key.rule.match.legacy.LegacyTacletMatcher;
import de.uka.ilkd.key.rule.match.vm.VMTacletMatcher;


/**
 * Abstract factory for the creation of taclet matcher.
 * 
 * Use method {@link #getKit()} to get the concrete factory and call {@link #createTacletMatcher(Taclet)}
 * to create a matcher for a {@link Taclet} 
 *
 * The active factory is chosen at runtime by passing a value for the system property <code>taclet.match</code>
 * Currently supported values are: {@code legacy} and {@code vm}. The legacy matching algorithm is
 * the one used since the beginning of KeY. It will soon become deprecated and replaced y {@code vm} as default.  
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
     * The concrete factory for the legacy taclet matcher.
     */
    private static final class LegacyTacletMatcherKit extends TacletMatcherKit {
        @Override
        public TacletMatcher createTacletMatcher(Taclet taclet) {
            return new LegacyTacletMatcher(taclet);
        }
    }

    /**
     * sets up the concrete factory to use depending on the provided system property or the given default if no
     * property is set
     */
    private static final String TACLET_MATCHER_SELECTION_VALUE = System.getProperty("taclet.match", "vm");    
    private static final TacletMatcherKit ACTIVE_TACLET_MATCHER_KIT; 
    static {    
        if ("legacy".equals(TACLET_MATCHER_SELECTION_VALUE)) {
            ACTIVE_TACLET_MATCHER_KIT = new LegacyTacletMatcherKit();
        } else {
            ACTIVE_TACLET_MATCHER_KIT = new VMTacletMatcherKit();
        }
    }

    /**
     * returns the currently enabled factory
     * @return the concrete factory to create taclet matchers
     */
    public static TacletMatcherKit getKit() {
        return ACTIVE_TACLET_MATCHER_KIT;
    }

    /**
     * the creator method returning the matcher for the specified taclet 
     * @param taclet the {@link Taclet} for which to create a matcher
     * @return the matcher for the given taclet
     */
    public abstract TacletMatcher createTacletMatcher(Taclet taclet);
}
