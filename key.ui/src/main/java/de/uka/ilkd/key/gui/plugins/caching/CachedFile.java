package de.uka.ilkd.key.gui.plugins.caching;

public final class CachedFile {
    /**
     * Name of this file. Always located in ~/.key/cachedProofs
     */
    public final String filename;
    public final int hash;

    public CachedFile(String filename, int hash) {
        this.filename = filename;
        this.hash = hash;
    }
}
