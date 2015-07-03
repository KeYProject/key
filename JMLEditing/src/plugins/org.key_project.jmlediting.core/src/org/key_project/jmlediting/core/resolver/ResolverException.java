package org.key_project.jmlediting.core.resolver;

/**
 * ResolverException is thrown, if the resolver can not read the IASTNode given.
 * 
 * @author Christopher Beckmann
 *
 */
public class ResolverException extends Exception {

    /**
     * 
     */
    private static final long serialVersionUID = 585636674455840351L;
    
    public ResolverException(final String string) {
        super(string);
    }

    public ResolverException(final String string, final Throwable e) {
        super(string, e);
    }
}
