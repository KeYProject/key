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
    
    /**
     * return the currently used factory for the {@link TacletIndex}
     * @return the concrete taclet index factory
     */
    public static TacletIndexKit getKit() {
        return ACTIVE_TACLET_INDEX_KIT;
    }
    
    /**
     * abstract factory method to create an empty {@link TacletIndex}
     * @return the created {@link TacletIndex}
     */
    public abstract TacletIndex createTacletIndex();

    /**
     * abstract factory method to create a {@link TacletIndex} containing the provided taclets
     * 
     * @return the created {@link TacletIndex}
     */
    public abstract TacletIndex createTacletIndex(Iterable<Taclet> tacletSet);
    

    /**
     * Concrete factory creating the single threaded version of the {@link TacletIndex} 
     */
    private static class SingleThreadedTacletIndexKit extends TacletIndexKit {
        
        public TacletIndex createTacletIndex() {
            return new SingleThreadedTacletIndex();
        }

        public TacletIndex createTacletIndex(Iterable<Taclet> tacletSet) {
            return new SingleThreadedTacletIndex(tacletSet);
        }
    }
    
    /**
     * Concrete factory creating the multi threaded version of the {@link TacletIndex}
     * (performs matching using multiple threads) 
     */
    private static class MultiThreadedTacletIndexKit extends TacletIndexKit {
        
        public TacletIndex createTacletIndex() {
            return new MultiThreadedTacletIndex();
        }

        public TacletIndex createTacletIndex(Iterable<Taclet> tacletSet) {
            return new MultiThreadedTacletIndex(tacletSet);
        }
    }

        
}
