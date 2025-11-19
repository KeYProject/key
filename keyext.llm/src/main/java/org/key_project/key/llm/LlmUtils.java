package org.key_project.key.llm;

import de.uka.ilkd.key.proof.Proof;

/**
 *
 * @author Alexander Weigl
 * @version 1 (11/18/25)
 */
public class LlmUtils {
    public static LlmSession getSession(Proof proof) {
        return getSession(LlmSettings.INSTANCE, proof);
    }

    public static LlmSession getSession(LlmSettings settings, Proof proof) {
        if (proof != null) {
            var session = proof.lookup(LlmSession.class);
            if (session != null) {
                return session;
            }
        }
        var session = new LlmSession(settings.getApiEndpoint(), settings.getAuthToken());
        if (proof != null) {
            proof.register(session, LlmSession.class);
        }
        return session;
    }
}
