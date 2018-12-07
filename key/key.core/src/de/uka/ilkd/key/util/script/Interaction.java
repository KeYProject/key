package de.uka.ilkd.key.util.script;

import java.io.Serializable;
import java.util.Date;

import de.uka.ilkd.key.java.Services;

/**
 * @author weigl
 */
public interface Interaction extends Serializable {
    Date created();
    default String getProofScriptRepresentation(Services services) {
        throw new UnsupportedOperationException();
    }
}
