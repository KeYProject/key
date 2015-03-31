package de.uka.ilkd.key.proof;

import de.uka.ilkd.key.rule.Taclet;

/**
 * Abstract factory for creating {@link TacletIndex} instances
 */
public abstract class TacletIndexKit {
    
    private static final TacletIndexKit ACTIVE_TACLET_INDEX_KIT;
    
    static {
        final String threading = System.getProperty("tacletindex.threading.enabled", "false");
        if ("true".equals(threading)) {
            ACTIVE_TACLET_INDEX_KIT = new MultiThreadedTacletIndexKit();
        } else {
            ACTIVE_TACLET_INDEX_KIT = new SingleThreadedTacletIndexKit();
        }
    }
    
    public static TacletIndexKit getKit() {
        return ACTIVE_TACLET_INDEX_KIT;
    }
    
    public abstract TacletIndex createTacletIndex();

    public abstract TacletIndex createTacletIndex(Iterable<Taclet> tacletSet);

    
    
    private static class SingleThreadedTacletIndexKit extends TacletIndexKit {
        
        public TacletIndex createTacletIndex() {
            return new SingleThreadedTacletIndex();
        }

        public TacletIndex createTacletIndex(Iterable<Taclet> tacletSet) {
            return new SingleThreadedTacletIndex(tacletSet);
        }
    }
    
    private static class MultiThreadedTacletIndexKit extends TacletIndexKit {
        
        public TacletIndex createTacletIndex() {
            return new MultiThreadedTacletIndex();
        }

        public TacletIndex createTacletIndex(Iterable<Taclet> tacletSet) {
            return new MultiThreadedTacletIndex(tacletSet);
        }
    }

        
}
