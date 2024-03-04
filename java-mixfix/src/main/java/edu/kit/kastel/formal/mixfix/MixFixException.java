/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 * 
 * The system is protected by the GNU General Public License. 
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

/**
 * MixFixException are thrown by {@link MixFixParser} when the result of a
 * parsing process is erroneous.
 * 
 * They always contain a reference to a token (retrieve via {@link #getToken()})
 * to which the parser pinned the execption. This assignment is not always
 * accurate.
 * 
 * If the exception stems from an instance of type
 * <code>MixFixParser&lt;T&gt;</code>, {@link #getToken()} is guaranteed to be
 * of type <code>T</code> also.
 * 
 * @author mattias ulbrich
 */
public class MixFixException extends Exception {
    private static final long serialVersionUID = -7898251715665380761L;
    
    private Object token;

    public MixFixException() {
        super();
    }

    public MixFixException(String message, Throwable cause) {
        super(message, cause);
    }

    public MixFixException(String message) {
        super(message);
    }

    public MixFixException(Throwable cause) {
        super(cause);
    }

    public MixFixException(String string, Object token) {
        super(string);
        this.token = token;
    }

    public Object getToken() {
        return token;
    }

}
